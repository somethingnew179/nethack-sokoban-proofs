import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame672 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 18, changes := [(56, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832829, afterBeta := 5439685, afterBonus := 5832828, preBeta := 5439685, preBonus := 5834352, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1340620, restrictionAfterBeta := 23, restrictionAfterBonus := 1340622, updateProofs := some (28, 377486), numericProof := 76240, slack := 0}
noncomputable def case672 : PhysicalCase := ⟨2,108,.north,.push 82 (.stay 56),frame672⟩
theorem frame672_checked : CountedLocalCaseData.check data frame672 = true := by decide +kernel
theorem case672_fitted : fits case672 = true := by decide +kernel
noncomputable def frame673 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 18, changes := [(108, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832827, afterBeta := 5439685, afterBonus := 5832828, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1340626, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (43, 377493), numericProof := 76241, slack := 2}
noncomputable def case673 : PhysicalCase := ⟨2,56,.south,.push 82 (.stay 108),frame673⟩
theorem frame673_checked : CountedLocalCaseData.check data frame673 = true := by decide +kernel
theorem case673_fitted : fits case673 = true := by decide +kernel
noncomputable def frame674 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 18, changes := [(82, true), (108, false)], beforeBeta := 5112151, beforeBonus := 5832830, afterBeta := 5439685, afterBonus := 5832829, preBeta := 5112151, preBonus := 5834354, restrictionBeforeBeta := 536, restrictionBeforeBonus := 1340633, restrictionAfterBeta := 536, restrictionAfterBonus := 1340638, updateProofs := some (65, 377501), numericProof := 76242, slack := 0}
noncomputable def case674 : PhysicalCase := ⟨2,134,.north,.push 108 (.stay 82),frame674⟩
theorem frame674_checked : CountedLocalCaseData.check data frame674 = true := by decide +kernel
theorem case674_fitted : fits case674 = true := by decide +kernel
noncomputable def frame675 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 18, changes := [(134, true), (108, false)], beforeBeta := 5439685, beforeBonus := 5832828, afterBeta := 5439685, afterBonus := 5832829, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 923716, restrictionBeforeBonus := 1340645, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (120, 377515), numericProof := 76243, slack := 2}
noncomputable def case675 : PhysicalCase := ⟨2,82,.south,.push 108 (.stay 134),frame675⟩
theorem frame675_checked : CountedLocalCaseData.check data frame675 = true := by decide +kernel
theorem case675_fitted : fits case675 = true := by decide +kernel
noncomputable def frame676 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 18, changes := [(117, true), (116, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (145, 121), numericProof := 76244, slack := 1}
noncomputable def case676 : PhysicalCase := ⟨2,115,.east,.push 116 (.stay 117),frame676⟩
theorem frame676_checked : CountedLocalCaseData.check data frame676 = true := by decide +kernel
theorem case676_fitted : fits case676 = true := by decide +kernel
noncomputable def frame677 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 18, changes := [(115, true), (116, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (165, 146), numericProof := 76244, slack := 1}
noncomputable def case677 : PhysicalCase := ⟨2,117,.west,.push 116 (.stay 115),frame677⟩
theorem frame677_checked : CountedLocalCaseData.check data frame677 = true := by decide +kernel
theorem case677_fitted : fits case677 = true := by decide +kernel
noncomputable def frame678 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 18, changes := [(105, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832835, afterBeta := 5439686, afterBonus := 5832835, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1340652, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (180, 377520), numericProof := 76245, slack := 1}
noncomputable def case678 : PhysicalCase := ⟨2,157,.north,.push 131 (.stay 105),frame678⟩
theorem frame678_checked : CountedLocalCaseData.check data frame678 = true := by decide +kernel
theorem case678_fitted : fits case678 = true := by decide +kernel
noncomputable def frame679 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 18, changes := [(157, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832835, afterBeta := 5439686, afterBonus := 5832835, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1340652, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (508, 377527), numericProof := 76245, slack := 1}
noncomputable def case679 : PhysicalCase := ⟨2,105,.south,.push 131 (.stay 157),frame679⟩
theorem frame679_checked : CountedLocalCaseData.check data frame679 = true := by decide +kernel
theorem case679_fitted : fits case679 = true := by decide +kernel
noncomputable def frame680 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 18, changes := [(106, true), (132, false)], beforeBeta := 5439693, beforeBonus := 5832841, afterBeta := 5439688, afterBonus := 5832834, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 923823, restrictionBeforeBonus := 1340659, restrictionAfterBeta := 923956, restrictionAfterBonus := 3, updateProofs := some (529, 377533), numericProof := 76246, slack := 12}
noncomputable def case680 : PhysicalCase := ⟨2,158,.north,.push 132 (.stay 106),frame680⟩
theorem frame680_checked : CountedLocalCaseData.check data frame680 = true := by decide +kernel
theorem case680_fitted : fits case680 = true := by decide +kernel
noncomputable def frame681 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 18, changes := [(158, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832835, afterBeta := 5439688, afterBonus := 5832834, preBeta := 5440591, preBonus := 5834357, restrictionBeforeBeta := 923959, restrictionBeforeBonus := 1340663, restrictionAfterBeta := 924014, restrictionAfterBonus := 1340667, updateProofs := some (826, 377540), numericProof := 76251, slack := 2}
noncomputable def case681 : PhysicalCase := ⟨2,106,.south,.push 132 (.stay 158),frame681⟩
theorem frame681_checked : CountedLocalCaseData.check data frame681 = true := by decide +kernel
theorem case681_fitted : fits case681 = true := by decide +kernel
noncomputable def frame682 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 18, changes := [(133, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832835, afterBeta := 5439688, afterBonus := 5832834, preBeta := 5440596, preBonus := 5834359, restrictionBeforeBeta := 924040, restrictionBeforeBonus := 1340674, restrictionAfterBeta := 924109, restrictionAfterBonus := 1340678, updateProofs := some (902, 377547), numericProof := 76256, slack := 0}
noncomputable def case682 : PhysicalCase := ⟨2,131,.east,.push 132 (.stay 133),frame682⟩
theorem frame682_checked : CountedLocalCaseData.check data frame682 = true := by decide +kernel
theorem case682_fitted : fits case682 = true := by decide +kernel
noncomputable def frame683 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 18, changes := [(131, true), (132, false)], beforeBeta := 5439689, beforeBonus := 5832832, afterBeta := 5439688, afterBonus := 5832834, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 924166, restrictionBeforeBonus := 1340682, restrictionAfterBeta := 924229, restrictionAfterBonus := 3, updateProofs := some (955, 377554), numericProof := 76257, slack := 12}
noncomputable def case683 : PhysicalCase := ⟨2,133,.west,.push 132 (.stay 131),frame683⟩
theorem frame683_checked : CountedLocalCaseData.check data frame683 = true := by decide +kernel
theorem case683_fitted : fits case683 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
