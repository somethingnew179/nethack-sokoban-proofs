import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame672 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 17, changes := [(30, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832856, afterBeta := 5439685, afterBonus := 5832855, preBeta := 5439685, preBonus := 5834669, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1342712, restrictionAfterBeta := 0, restrictionAfterBonus := 1342713, updateProofs := some (12, 378186), numericProof := 77013, slack := 0}
noncomputable def case672 : PhysicalCase := ⟨3,82,.north,.push 56 (.stay 30),frame672⟩
theorem frame672_checked : CountedLocalCaseData.check data frame672 = true := by decide +kernel
theorem case672_fitted : fits case672 = true := by decide +kernel
noncomputable def frame673 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 17, changes := [(82, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832854, afterBeta := 5439685, afterBonus := 5832855, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1342716, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (18, 378190), numericProof := 77014, slack := 2}
noncomputable def case673 : PhysicalCase := ⟨3,30,.south,.push 56 (.stay 82),frame673⟩
theorem frame673_checked : CountedLocalCaseData.check data frame673 = true := by decide +kernel
theorem case673_fitted : fits case673 = true := by decide +kernel
noncomputable def frame674 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 17, changes := [(56, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832857, afterBeta := 5439685, afterBonus := 5832856, preBeta := 5439685, preBonus := 5834671, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1342720, restrictionAfterBeta := 23, restrictionAfterBonus := 1342722, updateProofs := some (28, 378195), numericProof := 77015, slack := 0}
noncomputable def case674 : PhysicalCase := ⟨3,108,.north,.push 82 (.stay 56),frame674⟩
theorem frame674_checked : CountedLocalCaseData.check data frame674 = true := by decide +kernel
theorem case674_fitted : fits case674 = true := by decide +kernel
noncomputable def frame675 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 17, changes := [(108, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832855, afterBeta := 5439685, afterBonus := 5832856, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1342726, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (43, 378202), numericProof := 77016, slack := 2}
noncomputable def case675 : PhysicalCase := ⟨3,56,.south,.push 82 (.stay 108),frame675⟩
theorem frame675_checked : CountedLocalCaseData.check data frame675 = true := by decide +kernel
theorem case675_fitted : fits case675 = true := by decide +kernel
noncomputable def frame676 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 17, changes := [(82, true), (108, false)], beforeBeta := 5112151, beforeBonus := 5832858, afterBeta := 5439685, afterBonus := 5832857, preBeta := 5112151, preBonus := 5834673, restrictionBeforeBeta := 536, restrictionBeforeBonus := 1342733, restrictionAfterBeta := 536, restrictionAfterBonus := 1342736, updateProofs := some (65, 378206), numericProof := 77017, slack := 0}
noncomputable def case676 : PhysicalCase := ⟨3,134,.north,.push 108 (.stay 82),frame676⟩
theorem frame676_checked : CountedLocalCaseData.check data frame676 = true := by decide +kernel
theorem case676_fitted : fits case676 = true := by decide +kernel
noncomputable def frame677 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 17, changes := [(134, true), (108, false)], beforeBeta := 5439685, beforeBonus := 5832856, afterBeta := 5439685, afterBonus := 5832857, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 923716, restrictionBeforeBonus := 1342739, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (120, 378210), numericProof := 77018, slack := 2}
noncomputable def case677 : PhysicalCase := ⟨3,82,.south,.push 108 (.stay 134),frame677⟩
theorem frame677_checked : CountedLocalCaseData.check data frame677 = true := by decide +kernel
theorem case677_fitted : fits case677 = true := by decide +kernel
noncomputable def frame678 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 17, changes := [(117, true), (116, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (145, 121), numericProof := 77019, slack := 1}
noncomputable def case678 : PhysicalCase := ⟨3,115,.east,.push 116 (.stay 117),frame678⟩
theorem frame678_checked : CountedLocalCaseData.check data frame678 = true := by decide +kernel
theorem case678_fitted : fits case678 = true := by decide +kernel
noncomputable def frame679 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 17, changes := [(115, true), (116, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (165, 146), numericProof := 77019, slack := 1}
noncomputable def case679 : PhysicalCase := ⟨3,117,.west,.push 116 (.stay 115),frame679⟩
theorem frame679_checked : CountedLocalCaseData.check data frame679 = true := by decide +kernel
theorem case679_fitted : fits case679 = true := by decide +kernel
noncomputable def frame680 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 17, changes := [(105, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832868, afterBeta := 5439686, afterBonus := 5832868, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1342743, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (180, 378214), numericProof := 77020, slack := 1}
noncomputable def case680 : PhysicalCase := ⟨3,157,.north,.push 131 (.stay 105),frame680⟩
theorem frame680_checked : CountedLocalCaseData.check data frame680 = true := by decide +kernel
theorem case680_fitted : fits case680 = true := by decide +kernel
noncomputable def frame681 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 17, changes := [(157, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832868, afterBeta := 5439686, afterBonus := 5832868, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1342743, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (508, 378218), numericProof := 77020, slack := 1}
noncomputable def case681 : PhysicalCase := ⟨3,105,.south,.push 131 (.stay 157),frame681⟩
theorem frame681_checked : CountedLocalCaseData.check data frame681 = true := by decide +kernel
theorem case681_fitted : fits case681 = true := by decide +kernel
noncomputable def frame682 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 17, changes := [(106, true), (132, false)], beforeBeta := 5439693, beforeBonus := 5832863, afterBeta := 5439688, afterBonus := 5832869, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 923823, restrictionBeforeBonus := 1342747, restrictionAfterBeta := 923956, restrictionAfterBonus := 3, updateProofs := some (529, 378222), numericProof := 77021, slack := 12}
noncomputable def case682 : PhysicalCase := ⟨3,158,.north,.push 132 (.stay 106),frame682⟩
theorem frame682_checked : CountedLocalCaseData.check data frame682 = true := by decide +kernel
theorem case682_fitted : fits case682 = true := by decide +kernel
noncomputable def frame683 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 17, changes := [(158, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832868, afterBeta := 5439688, afterBonus := 5832869, preBeta := 5440591, preBonus := 5834676, restrictionBeforeBeta := 923959, restrictionBeforeBonus := 1342750, restrictionAfterBeta := 924014, restrictionAfterBonus := 1342753, updateProofs := some (826, 378226), numericProof := 77025, slack := 2}
noncomputable def case683 : PhysicalCase := ⟨3,106,.south,.push 132 (.stay 158),frame683⟩
theorem frame683_checked : CountedLocalCaseData.check data frame683 = true := by decide +kernel
theorem case683_fitted : fits case683 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
