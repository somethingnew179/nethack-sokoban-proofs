import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame672 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 19, changes := [(82, true), (108, false)], beforeBeta := 5112151, beforeBonus := 5832773, afterBeta := 5439685, afterBonus := 5832772, preBeta := 5112151, preBonus := 5833898, restrictionBeforeBeta := 536, restrictionBeforeBonus := 1336174, restrictionAfterBeta := 536, restrictionAfterBonus := 1336179, updateProofs := some (65, 375485), numericProof := 75096, slack := 0}
noncomputable def case672 : PhysicalCase := ⟨1,134,.north,.push 108 (.stay 82),frame672⟩
theorem frame672_checked : CountedLocalCaseData.check data frame672 = true := by decide +kernel
theorem case672_fitted : fits case672 = true := by decide +kernel
noncomputable def frame673 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 19, changes := [(134, true), (108, false)], beforeBeta := 5439685, beforeBonus := 5832771, afterBeta := 5439685, afterBonus := 5832772, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 923716, restrictionBeforeBonus := 1336186, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (120, 375502), numericProof := 75097, slack := 2}
noncomputable def case673 : PhysicalCase := ⟨1,82,.south,.push 108 (.stay 134),frame673⟩
theorem frame673_checked : CountedLocalCaseData.check data frame673 = true := by decide +kernel
theorem case673_fitted : fits case673 = true := by decide +kernel
noncomputable def frame674 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 19, changes := [(117, true), (116, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439687, afterBonus := 5832808, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336188, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (145, 375504), numericProof := 75098, slack := 1}
noncomputable def case674 : PhysicalCase := ⟨1,115,.east,.push 116 (.stay 117),frame674⟩
theorem frame674_checked : CountedLocalCaseData.check data frame674 = true := by decide +kernel
theorem case674_fitted : fits case674 = true := by decide +kernel
noncomputable def frame675 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 19, changes := [(115, true), (116, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439687, afterBonus := 5832808, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336188, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (165, 375506), numericProof := 75098, slack := 1}
noncomputable def case675 : PhysicalCase := ⟨1,117,.west,.push 116 (.stay 115),frame675⟩
theorem frame675_checked : CountedLocalCaseData.check data frame675 = true := by decide +kernel
theorem case675_fitted : fits case675 = true := by decide +kernel
noncomputable def frame676 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 19, changes := [(105, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832779, afterBeta := 5439686, afterBonus := 5832779, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1336203, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (180, 375511), numericProof := 75099, slack := 1}
noncomputable def case676 : PhysicalCase := ⟨1,157,.north,.push 131 (.stay 105),frame676⟩
theorem frame676_checked : CountedLocalCaseData.check data frame676 = true := by decide +kernel
theorem case676_fitted : fits case676 = true := by decide +kernel
noncomputable def frame677 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 19, changes := [(157, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832779, afterBeta := 5439686, afterBonus := 5832779, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1336203, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (508, 375530), numericProof := 75099, slack := 1}
noncomputable def case677 : PhysicalCase := ⟨1,105,.south,.push 131 (.stay 157),frame677⟩
theorem frame677_checked : CountedLocalCaseData.check data frame677 = true := by decide +kernel
theorem case677_fitted : fits case677 = true := by decide +kernel
noncomputable def frame678 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 19, changes := [(106, true), (132, false)], beforeBeta := 5439693, beforeBonus := 5832803, afterBeta := 5439688, afterBonus := 5832778, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 923823, restrictionBeforeBonus := 1336220, restrictionAfterBeta := 923956, restrictionAfterBonus := 3, updateProofs := some (529, 375536), numericProof := 75100, slack := 12}
noncomputable def case678 : PhysicalCase := ⟨1,158,.north,.push 132 (.stay 106),frame678⟩
theorem frame678_checked : CountedLocalCaseData.check data frame678 = true := by decide +kernel
theorem case678_fitted : fits case678 = true := by decide +kernel
noncomputable def frame679 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 19, changes := [(158, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832779, afterBeta := 5439688, afterBonus := 5832778, preBeta := 5440591, preBonus := 5833901, restrictionBeforeBeta := 923959, restrictionBeforeBonus := 1336232, restrictionAfterBeta := 924014, restrictionAfterBonus := 1336239, updateProofs := some (826, 375556), numericProof := 75106, slack := 2}
noncomputable def case679 : PhysicalCase := ⟨1,106,.south,.push 132 (.stay 158),frame679⟩
theorem frame679_checked : CountedLocalCaseData.check data frame679 = true := by decide +kernel
theorem case679_fitted : fits case679 = true := by decide +kernel
noncomputable def frame680 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 19, changes := [(133, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832779, afterBeta := 5439688, afterBonus := 5832778, preBeta := 5440596, preBonus := 5833903, restrictionBeforeBeta := 924040, restrictionBeforeBonus := 1336256, restrictionAfterBeta := 924109, restrictionAfterBonus := 1336263, updateProofs := some (902, 375575), numericProof := 75112, slack := 0}
noncomputable def case680 : PhysicalCase := ⟨1,131,.east,.push 132 (.stay 133),frame680⟩
theorem frame680_checked : CountedLocalCaseData.check data frame680 = true := by decide +kernel
theorem case680_fitted : fits case680 = true := by decide +kernel
noncomputable def frame681 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 19, changes := [(131, true), (132, false)], beforeBeta := 5439689, beforeBonus := 5832775, afterBeta := 5439688, afterBonus := 5832778, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 924166, restrictionBeforeBonus := 1336275, restrictionAfterBeta := 924229, restrictionAfterBonus := 3, updateProofs := some (955, 375590), numericProof := 75113, slack := 12}
noncomputable def case681 : PhysicalCase := ⟨1,133,.west,.push 132 (.stay 131),frame681⟩
theorem frame681_checked : CountedLocalCaseData.check data frame681 = true := by decide +kernel
theorem case681_fitted : fits case681 = true := by decide +kernel
noncomputable def frame682 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 19, changes := [(134, true), (133, false)], beforeBeta := 5439688, beforeBonus := 5832778, afterBeta := 5439689, afterBonus := 5832775, preBeta := 5440615, preBonus := 5833907, restrictionBeforeBeta := 924238, restrictionBeforeBonus := 1336294, restrictionAfterBeta := 924312, restrictionAfterBonus := 1336306, updateProofs := some (1060, 375609), numericProof := 75119, slack := 0}
noncomputable def case682 : PhysicalCase := ⟨1,132,.east,.push 133 (.stay 134),frame682⟩
theorem frame682_checked : CountedLocalCaseData.check data frame682 = true := by decide +kernel
theorem case682_fitted : fits case682 = true := by decide +kernel
noncomputable def frame683 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 19, changes := [(132, true), (133, false)], beforeBeta := 5112151, beforeBonus := 5832773, afterBeta := 5439689, afterBonus := 5832775, preBeta := 5440606, preBonus := 5833910, restrictionBeforeBeta := 924356, restrictionBeforeBonus := 1336321, restrictionAfterBeta := 924402, restrictionAfterBonus := 1336328, updateProofs := some (1136, 375626), numericProof := 75120, slack := 2}
noncomputable def case683 : PhysicalCase := ⟨1,134,.west,.push 133 (.stay 132),frame683⟩
theorem frame683_checked : CountedLocalCaseData.check data frame683 = true := by decide +kernel
theorem case683_fitted : fits case683 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
