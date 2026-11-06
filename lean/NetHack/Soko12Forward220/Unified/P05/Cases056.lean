import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame672 : CountedLocalCase.Frame := {bindings := [(400, false)], budget := 15, changes := [], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := none, numericProof := 78131, slack := 0}
noncomputable def case672 : PhysicalCase := ⟨5,400,.west,.walk 399,frame672⟩
theorem frame672_checked : CountedLocalCaseData.check data frame672 = true := by decide +kernel
theorem case672_fitted : fits case672 = true := by decide +kernel
noncomputable def frame673 : CountedLocalCase.Frame := {bindings := [(373, false), (400, false)], budget := 15, changes := [], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := none, numericProof := 78128, slack := 0}
noncomputable def case673 : PhysicalCase := ⟨5,400,.northWest,.walk 373,frame673⟩
theorem frame673_checked : CountedLocalCaseData.check data frame673 = true := by decide +kernel
theorem case673_fitted : fits case673 = true := by decide +kernel
noncomputable def frame674 : CountedLocalCase.Frame := {bindings := [(29, false), (30, true)], budget := 15, changes := [(30, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 0, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1345039, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (4, 2), numericProof := 78132, slack := 0}
noncomputable def case674 : PhysicalCase := ⟨5,29,.east,.push 30 (.fill 37),frame674⟩
theorem frame674_checked : CountedLocalCaseData.check data frame674 = true := by decide +kernel
theorem case674_fitted : fits case674 = true := by decide +kernel
noncomputable def frame675 : CountedLocalCase.Frame := {bindings := [(29, false), (30, true)], budget := 15, changes := [(29, true), (30, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1345039, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (6, 378903), numericProof := 78133, slack := 18}
noncomputable def case675 : PhysicalCase := ⟨5,31,.west,.push 30 (.stay 29),frame675⟩
theorem frame675_checked : CountedLocalCaseData.check data frame675 = true := by decide +kernel
theorem case675_fitted : fits case675 = true := by decide +kernel
noncomputable def frame676 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 15, changes := [(30, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1345042, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (12, 378905), numericProof := 78134, slack := 0}
noncomputable def case676 : PhysicalCase := ⟨5,82,.north,.push 56 (.stay 30),frame676⟩
theorem frame676_checked : CountedLocalCaseData.check data frame676 = true := by decide +kernel
theorem case676_fitted : fits case676 = true := by decide +kernel
noncomputable def frame677 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 15, changes := [(82, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1345042, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (18, 378907), numericProof := 78135, slack := 2}
noncomputable def case677 : PhysicalCase := ⟨5,30,.south,.push 56 (.stay 82),frame677⟩
theorem frame677_checked : CountedLocalCaseData.check data frame677 = true := by decide +kernel
theorem case677_fitted : fits case677 = true := by decide +kernel
noncomputable def frame678 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 15, changes := [(56, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1345044, restrictionAfterBeta := 23, restrictionAfterBonus := 3, updateProofs := some (28, 378909), numericProof := 78136, slack := 0}
noncomputable def case678 : PhysicalCase := ⟨5,108,.north,.push 82 (.stay 56),frame678⟩
theorem frame678_checked : CountedLocalCaseData.check data frame678 = true := by decide +kernel
theorem case678_fitted : fits case678 = true := by decide +kernel
noncomputable def frame679 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 15, changes := [(108, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1345044, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (43, 378911), numericProof := 78137, slack := 2}
noncomputable def case679 : PhysicalCase := ⟨5,56,.south,.push 82 (.stay 108),frame679⟩
theorem frame679_checked : CountedLocalCaseData.check data frame679 = true := by decide +kernel
theorem case679_fitted : fits case679 = true := by decide +kernel
noncomputable def frame680 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 15, changes := [(82, true), (108, false)], beforeBeta := 5112151, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 5112151, preBonus := 0, restrictionBeforeBeta := 536, restrictionBeforeBonus := 1345046, restrictionAfterBeta := 536, restrictionAfterBonus := 3, updateProofs := some (65, 378913), numericProof := 78138, slack := 0}
noncomputable def case680 : PhysicalCase := ⟨5,134,.north,.push 108 (.stay 82),frame680⟩
theorem frame680_checked : CountedLocalCaseData.check data frame680 = true := by decide +kernel
theorem case680_fitted : fits case680 = true := by decide +kernel
noncomputable def frame681 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 15, changes := [(134, true), (108, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5439685, afterBonus := 5832909, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 923716, restrictionBeforeBonus := 1345046, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (120, 378915), numericProof := 78139, slack := 2}
noncomputable def case681 : PhysicalCase := ⟨5,82,.south,.push 108 (.stay 134),frame681⟩
theorem frame681_checked : CountedLocalCaseData.check data frame681 = true := by decide +kernel
theorem case681_fitted : fits case681 = true := by decide +kernel
noncomputable def frame682 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 15, changes := [(117, true), (116, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (145, 121), numericProof := 78140, slack := 1}
noncomputable def case682 : PhysicalCase := ⟨5,115,.east,.push 116 (.stay 117),frame682⟩
theorem frame682_checked : CountedLocalCaseData.check data frame682 = true := by decide +kernel
theorem case682_fitted : fits case682 = true := by decide +kernel
noncomputable def frame683 : CountedLocalCase.Frame := {bindings := [(115, false), (116, true), (117, false)], budget := 15, changes := [(115, true), (116, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (165, 146), numericProof := 78140, slack := 1}
noncomputable def case683 : PhysicalCase := ⟨5,117,.west,.push 116 (.stay 115),frame683⟩
theorem frame683_checked : CountedLocalCaseData.check data frame683 = true := by decide +kernel
theorem case683_fitted : fits case683 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
