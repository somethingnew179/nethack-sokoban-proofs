import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame720 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 15, changes := [(140, true), (166, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (10275, 10106), numericProof := 78182, slack := 3}
noncomputable def case720 : PhysicalCase := ⟨5,192,.north,.push 166 (.stay 140),frame720⟩
theorem frame720_checked : CountedLocalCaseData.check data frame720 = true := by decide +kernel
theorem case720_fitted : fits case720 = true := by decide +kernel
noncomputable def frame721 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 15, changes := [(192, true), (166, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (12136, 10276), numericProof := 78183, slack := 0}
noncomputable def case721 : PhysicalCase := ⟨5,140,.south,.push 166 (.stay 192),frame721⟩
theorem frame721_checked : CountedLocalCaseData.check data frame721 = true := by decide +kernel
theorem case721_fitted : fits case721 = true := by decide +kernel
noncomputable def frame722 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 15, changes := [(141, true), (167, false)], beforeBeta := 5439700, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440660, preBonus := 0, restrictionBeforeBeta := 935413, restrictionBeforeBonus := 3, restrictionAfterBeta := 935914, restrictionAfterBonus := 3, updateProofs := some (12436, 12137), numericProof := 78184, slack := 2}
noncomputable def case722 : PhysicalCase := ⟨5,193,.north,.push 167 (.stay 141),frame722⟩
theorem frame722_checked : CountedLocalCaseData.check data frame722 = true := by decide +kernel
theorem case722_fitted : fits case722 = true := by decide +kernel
noncomputable def frame723 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 15, changes := [(193, true), (167, false)], beforeBeta := 5439692, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440866, preBonus := 0, restrictionBeforeBeta := 936118, restrictionBeforeBonus := 3, restrictionAfterBeta := 936723, restrictionAfterBonus := 3, updateProofs := some (14425, 12437), numericProof := 78185, slack := 0}
noncomputable def case723 : PhysicalCase := ⟨5,141,.south,.push 167 (.stay 193),frame723⟩
theorem frame723_checked : CountedLocalCaseData.check data frame723 = true := by decide +kernel
theorem case723_fitted : fits case723 = true := by decide +kernel
noncomputable def frame724 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 15, changes := [(168, true), (167, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440874, preBonus := 0, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 3, restrictionAfterBeta := 937363, restrictionAfterBonus := 3, updateProofs := some (15015, 14426), numericProof := 78186, slack := 2}
noncomputable def case724 : PhysicalCase := ⟨5,166,.east,.push 167 (.stay 168),frame724⟩
theorem frame724_checked : CountedLocalCaseData.check data frame724 = true := by decide +kernel
theorem case724_fitted : fits case724 = true := by decide +kernel
noncomputable def frame725 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 15, changes := [(166, true), (167, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 14070, restrictionAfterBonus := 3, updateProofs := some (15520, 15016), numericProof := 78187, slack := 0}
noncomputable def case725 : PhysicalCase := ⟨5,168,.west,.push 167 (.stay 166),frame725⟩
theorem frame725_checked : CountedLocalCaseData.check data frame725 = true := by decide +kernel
theorem case725_fitted : fits case725 = true := by decide +kernel
noncomputable def frame726 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 15, changes := [(142, true), (168, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (15994, 15521), numericProof := 78188, slack := 1}
noncomputable def case726 : PhysicalCase := ⟨5,194,.north,.push 168 (.stay 142),frame726⟩
theorem frame726_checked : CountedLocalCaseData.check data frame726 = true := by decide +kernel
theorem case726_fitted : fits case726 = true := by decide +kernel
noncomputable def frame727 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 15, changes := [(194, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (17937, 15995), numericProof := 78189, slack := 1}
noncomputable def case727 : PhysicalCase := ⟨5,142,.south,.push 168 (.stay 194),frame727⟩
theorem frame727_checked : CountedLocalCaseData.check data frame727 = true := by decide +kernel
theorem case727_fitted : fits case727 = true := by decide +kernel
noncomputable def frame728 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 15, changes := [(169, true), (168, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (18552, 17938), numericProof := 78190, slack := 1}
noncomputable def case728 : PhysicalCase := ⟨5,167,.east,.push 168 (.stay 169),frame728⟩
theorem frame728_checked : CountedLocalCaseData.check data frame728 = true := by decide +kernel
theorem case728_fitted : fits case728 = true := by decide +kernel
noncomputable def frame729 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 15, changes := [(167, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (19099, 18553), numericProof := 78191, slack := 0}
noncomputable def case729 : PhysicalCase := ⟨5,169,.west,.push 168 (.stay 167),frame729⟩
theorem frame729_checked : CountedLocalCaseData.check data frame729 = true := by decide +kernel
theorem case729_fitted : fits case729 = true := by decide +kernel
noncomputable def frame730 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 15, changes := [(158, true), (184, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832910, preBeta := 5440906, preBonus := 0, restrictionBeforeBeta := 16512, restrictionBeforeBonus := 1345096, restrictionAfterBeta := 941678, restrictionAfterBonus := 3, updateProofs := some (19818, 378969), numericProof := 78192, slack := 0}
noncomputable def case730 : PhysicalCase := ⟨5,210,.north,.push 184 (.stay 158),frame730⟩
theorem frame730_checked : CountedLocalCaseData.check data frame730 = true := by decide +kernel
theorem case730_fitted : fits case730 = true := by decide +kernel
noncomputable def frame731 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 15, changes := [(210, true), (184, false)], beforeBeta := 5439693, beforeBonus := 5832910, afterBeta := 5439691, afterBonus := 5832910, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 2891, restrictionBeforeBonus := 1345098, restrictionAfterBeta := 16512, restrictionAfterBonus := 3, updateProofs := some (20869, 378971), numericProof := 78193, slack := 2}
noncomputable def case731 : PhysicalCase := ⟨5,158,.south,.push 184 (.stay 210),frame731⟩
theorem frame731_checked : CountedLocalCaseData.check data frame731 = true := by decide +kernel
theorem case731_fitted : fits case731 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
