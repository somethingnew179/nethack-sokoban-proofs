import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame780 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 18, changes := [(220, true), (219, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (125145, 121218), numericProof := 76602, slack := 2}
noncomputable def case780 : PhysicalCase := ⟨2,218,.east,.push 219 (.stay 220),frame780⟩
theorem frame780_checked : CountedLocalCaseData.check data frame780 = true := by decide +kernel
theorem case780_fitted : fits case780 = true := by decide +kernel
noncomputable def frame781 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 18, changes := [(218, true), (219, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (129041, 125146), numericProof := 76603, slack := 0}
noncomputable def case781 : PhysicalCase := ⟨2,220,.west,.push 219 (.stay 218),frame781⟩
theorem frame781_checked : CountedLocalCaseData.check data frame781 = true := by decide +kernel
theorem case781_fitted : fits case781 = true := by decide +kernel
noncomputable def frame782 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 18, changes := [(194, true), (220, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (131971, 129042), numericProof := 76604, slack := 1}
noncomputable def case782 : PhysicalCase := ⟨2,246,.north,.push 220 (.stay 194),frame782⟩
theorem frame782_checked : CountedLocalCaseData.check data frame782 = true := by decide +kernel
theorem case782_fitted : fits case782 = true := by decide +kernel
noncomputable def frame783 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 18, changes := [(246, true), (220, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (137164, 131972), numericProof := 76604, slack := 1}
noncomputable def case783 : PhysicalCase := ⟨2,194,.south,.push 220 (.stay 246),frame783⟩
theorem frame783_checked : CountedLocalCaseData.check data frame783 = true := by decide +kernel
theorem case783_fitted : fits case783 = true := by decide +kernel
noncomputable def frame784 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 18, changes := [(210, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 5834464, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341146, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341150, updateProofs := some (138557, 377849), numericProof := 76605, slack := 0}
noncomputable def case784 : PhysicalCase := ⟨2,262,.north,.push 236 (.stay 210),frame784⟩
theorem frame784_checked : CountedLocalCaseData.check data frame784 = true := by decide +kernel
theorem case784_fitted : fits case784 = true := by decide +kernel
noncomputable def frame785 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 18, changes := [(262, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832844, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341154, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (140071, 377856), numericProof := 76606, slack := 2}
noncomputable def case785 : PhysicalCase := ⟨2,210,.south,.push 236 (.stay 262),frame785⟩
theorem frame785_checked : CountedLocalCaseData.check data frame785 = true := by decide +kernel
theorem case785_fitted : fits case785 = true := by decide +kernel
noncomputable def frame786 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 18, changes := [(211, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832846, afterBeta := 5439691, afterBonus := 5832847, preBeta := 5439691, preBonus := 5834466, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341161, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341165, updateProofs := some (141440, 377863), numericProof := 76607, slack := 0}
noncomputable def case786 : PhysicalCase := ⟨2,263,.north,.push 237 (.stay 211),frame786⟩
theorem frame786_checked : CountedLocalCaseData.check data frame786 = true := by decide +kernel
theorem case786_fitted : fits case786 = true := by decide +kernel
noncomputable def frame787 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 18, changes := [(263, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832843, afterBeta := 5439691, afterBonus := 5832847, preBeta := 5439691, preBonus := 5834468, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341169, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341173, updateProofs := some (142896, 377870), numericProof := 76608, slack := 2}
noncomputable def case787 : PhysicalCase := ⟨2,211,.south,.push 237 (.stay 263),frame787⟩
theorem frame787_checked : CountedLocalCaseData.check data frame787 = true := by decide +kernel
theorem case787_fitted : fits case787 = true := by decide +kernel
noncomputable def frame788 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 18, changes := [(238, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832847, preBeta := 5439691, preBonus := 5834471, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341180, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341187, updateProofs := some (144294, 377877), numericProof := 76614, slack := 0}
noncomputable def case788 : PhysicalCase := ⟨2,236,.east,.push 237 (.stay 238),frame788⟩
theorem frame788_checked : CountedLocalCaseData.check data frame788 = true := by decide +kernel
theorem case788_fitted : fits case788 = true := by decide +kernel
noncomputable def frame789 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 18, changes := [(236, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832850, afterBeta := 5439691, afterBonus := 5832847, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341194, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (145671, 377884), numericProof := 76615, slack := 2}
noncomputable def case789 : PhysicalCase := ⟨2,238,.west,.push 237 (.stay 236),frame789⟩
theorem frame789_checked : CountedLocalCaseData.check data frame789 = true := by decide +kernel
theorem case789_fitted : fits case789 = true := by decide +kernel
noncomputable def frame790 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 18, changes := [(212, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832848, afterBeta := 5439691, afterBonus := 5832850, preBeta := 5439691, preBonus := 5834475, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341201, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341205, updateProofs := some (146345, 377891), numericProof := 76616, slack := 0}
noncomputable def case790 : PhysicalCase := ⟨2,264,.north,.push 238 (.stay 212),frame790⟩
theorem frame790_checked : CountedLocalCaseData.check data frame790 = true := by decide +kernel
theorem case790_fitted : fits case790 = true := by decide +kernel
noncomputable def frame791 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 18, changes := [(264, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832839, afterBeta := 5439691, afterBonus := 5832850, preBeta := 5439691, preBonus := 5834477, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341212, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341216, updateProofs := some (147122, 377898), numericProof := 76617, slack := 2}
noncomputable def case791 : PhysicalCase := ⟨2,212,.south,.push 238 (.stay 264),frame791⟩
theorem frame791_checked : CountedLocalCaseData.check data frame791 = true := by decide +kernel
theorem case791_fitted : fits case791 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
