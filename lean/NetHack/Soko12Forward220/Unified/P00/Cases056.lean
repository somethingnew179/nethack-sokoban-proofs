import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame672 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 20, changes := [(117, true), (116, false)], beforeBeta := 5439687, beforeBonus := 5832735, afterBeta := 5439687, afterBonus := 5832732, preBeta := 5439687, preBonus := 5833234, restrictionBeforeBeta := 829, restrictionBeforeBonus := 923746, restrictionAfterBeta := 829, restrictionAfterBonus := 923755, updateProofs := some (145, 142), numericProof := 900, slack := 1}
noncomputable def case672 : PhysicalCase := ⟨0,115,.east,.push 116 (.stay 117),frame672⟩
theorem frame672_checked : CountedLocalCaseData.check data frame672 = true := by decide +kernel
theorem case672_fitted : fits case672 = true := by decide +kernel
noncomputable def frame673 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 20, changes := [(115, true), (116, false)], beforeBeta := 5439687, beforeBonus := 5832731, afterBeta := 5439687, afterBonus := 5832732, preBeta := 5439687, preBonus := 5833237, restrictionBeforeBeta := 829, restrictionBeforeBonus := 923766, restrictionAfterBeta := 829, restrictionAfterBonus := 923773, updateProofs := some (165, 162), numericProof := 1049, slack := 1}
noncomputable def case673 : PhysicalCase := ⟨0,117,.west,.push 116 (.stay 115),frame673⟩
theorem frame673_checked : CountedLocalCaseData.check data frame673 = true := by decide +kernel
theorem case673_fitted : fits case673 = true := by decide +kernel
noncomputable def frame674 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 20, changes := [(105, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832761, afterBeta := 5439686, afterBonus := 5832761, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 923820, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (180, 177), numericProof := 1050, slack := 1}
noncomputable def case674 : PhysicalCase := ⟨0,157,.north,.push 131 (.stay 105),frame674⟩
theorem frame674_checked : CountedLocalCaseData.check data frame674 = true := by decide +kernel
theorem case674_fitted : fits case674 = true := by decide +kernel
noncomputable def frame675 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 20, changes := [(157, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832761, afterBeta := 5439686, afterBonus := 5832761, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 923820, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (508, 475), numericProof := 1050, slack := 1}
noncomputable def case675 : PhysicalCase := ⟨0,105,.south,.push 131 (.stay 157),frame675⟩
theorem frame675_checked : CountedLocalCaseData.check data frame675 = true := by decide +kernel
theorem case675_fitted : fits case675 = true := by decide +kernel
noncomputable def frame676 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 20, changes := [(106, true), (132, false)], beforeBeta := 5439693, beforeBonus := 5832762, afterBeta := 5439688, afterBonus := 5832760, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 923823, restrictionBeforeBonus := 923955, restrictionAfterBeta := 923956, restrictionAfterBonus := 3, updateProofs := some (529, 524), numericProof := 1051, slack := 12}
noncomputable def case676 : PhysicalCase := ⟨0,158,.north,.push 132 (.stay 106),frame676⟩
theorem frame676_checked : CountedLocalCaseData.check data frame676 = true := by decide +kernel
theorem case676_fitted : fits case676 = true := by decide +kernel
noncomputable def frame677 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 20, changes := [(158, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832761, afterBeta := 5439688, afterBonus := 5832760, preBeta := 5440591, preBonus := 5833241, restrictionBeforeBeta := 923959, restrictionBeforeBonus := 924013, restrictionAfterBeta := 924014, restrictionAfterBonus := 924033, updateProofs := some (826, 791), numericProof := 1856, slack := 2}
noncomputable def case677 : PhysicalCase := ⟨0,106,.south,.push 132 (.stay 158),frame677⟩
theorem frame677_checked : CountedLocalCaseData.check data frame677 = true := by decide +kernel
theorem case677_fitted : fits case677 = true := by decide +kernel
noncomputable def frame678 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 20, changes := [(133, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832761, afterBeta := 5439688, afterBonus := 5832760, preBeta := 5440596, preBonus := 5833243, restrictionBeforeBeta := 924040, restrictionBeforeBonus := 924108, restrictionAfterBeta := 924109, restrictionAfterBonus := 924161, updateProofs := some (902, 895), numericProof := 2070, slack := 0}
noncomputable def case678 : PhysicalCase := ⟨0,131,.east,.push 132 (.stay 133),frame678⟩
theorem frame678_checked : CountedLocalCaseData.check data frame678 = true := by decide +kernel
theorem case678_fitted : fits case678 = true := by decide +kernel
noncomputable def frame679 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 20, changes := [(131, true), (132, false)], beforeBeta := 5439689, beforeBonus := 5832755, afterBeta := 5439688, afterBonus := 5832760, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 924166, restrictionBeforeBonus := 924228, restrictionAfterBeta := 924229, restrictionAfterBonus := 3, updateProofs := some (955, 950), numericProof := 2071, slack := 12}
noncomputable def case679 : PhysicalCase := ⟨0,133,.west,.push 132 (.stay 131),frame679⟩
theorem frame679_checked : CountedLocalCaseData.check data frame679 = true := by decide +kernel
theorem case679_fitted : fits case679 = true := by decide +kernel
noncomputable def frame680 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 20, changes := [(134, true), (133, false)], beforeBeta := 5439688, beforeBonus := 5832760, afterBeta := 5439689, afterBonus := 5832755, preBeta := 5440615, preBonus := 5833247, restrictionBeforeBeta := 924238, restrictionBeforeBonus := 924309, restrictionAfterBeta := 924312, restrictionAfterBonus := 924354, updateProofs := some (1060, 1046), numericProof := 3081, slack := 0}
noncomputable def case680 : PhysicalCase := ⟨0,132,.east,.push 133 (.stay 134),frame680⟩
theorem frame680_checked : CountedLocalCaseData.check data frame680 = true := by decide +kernel
theorem case680_fitted : fits case680 = true := by decide +kernel
noncomputable def frame681 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 20, changes := [(132, true), (133, false)], beforeBeta := 5112151, beforeBonus := 5832752, afterBeta := 5439689, afterBonus := 5832755, preBeta := 5440606, preBonus := 5833250, restrictionBeforeBeta := 924356, restrictionBeforeBonus := 924401, restrictionAfterBeta := 924402, restrictionAfterBonus := 924449, updateProofs := some (1136, 1129), numericProof := 3082, slack := 2}
noncomputable def case681 : PhysicalCase := ⟨0,134,.west,.push 133 (.stay 132),frame681⟩
theorem frame681_checked : CountedLocalCaseData.check data frame681 = true := by decide +kernel
theorem case681_fitted : fits case681 = true := by decide +kernel
noncomputable def frame682 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 20, changes := [(108, true), (134, false)], beforeBeta := 5439695, beforeBonus := 5832747, afterBeta := 5112151, afterBonus := 5832752, preBeta := 5112183, preBonus := 5833253, restrictionBeforeBeta := 924450, restrictionBeforeBonus := 924521, restrictionAfterBeta := 924524, restrictionAfterBonus := 924567, updateProofs := some (1218, 1210), numericProof := 3190, slack := 0}
noncomputable def case682 : PhysicalCase := ⟨0,160,.north,.push 134 (.stay 108),frame682⟩
theorem frame682_checked : CountedLocalCaseData.check data frame682 = true := by decide +kernel
theorem case682_fitted : fits case682 = true := by decide +kernel
noncomputable def frame683 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 20, changes := [(160, true), (134, false)], beforeBeta := 5439685, beforeBonus := 5832759, afterBeta := 5112151, afterBonus := 5832752, preBeta := 5113909, preBonus := 5833256, restrictionBeforeBeta := 924573, restrictionBeforeBonus := 924619, restrictionAfterBeta := 924620, restrictionAfterBonus := 924642, updateProofs := some (1493, 1477), numericProof := 3675, slack := 2}
noncomputable def case683 : PhysicalCase := ⟨0,108,.south,.push 134 (.stay 160),frame683⟩
theorem frame683_checked : CountedLocalCaseData.check data frame683 = true := by decide +kernel
theorem case683_fitted : fits case683 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
