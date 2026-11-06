import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame720 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 18, changes := [(142, true), (168, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (15994, 15521), numericProof := 76442, slack := 1}
noncomputable def case720 : PhysicalCase := ⟨2,194,.north,.push 168 (.stay 142),frame720⟩
theorem frame720_checked : CountedLocalCaseData.check data frame720 = true := by decide +kernel
theorem case720_fitted : fits case720 = true := by decide +kernel
noncomputable def frame721 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 18, changes := [(194, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (17937, 15995), numericProof := 76443, slack := 1}
noncomputable def case721 : PhysicalCase := ⟨2,142,.south,.push 168 (.stay 194),frame721⟩
theorem frame721_checked : CountedLocalCaseData.check data frame721 = true := by decide +kernel
theorem case721_fitted : fits case721 = true := by decide +kernel
noncomputable def frame722 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 18, changes := [(169, true), (168, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (18552, 17938), numericProof := 76444, slack := 1}
noncomputable def case722 : PhysicalCase := ⟨2,167,.east,.push 168 (.stay 169),frame722⟩
theorem frame722_checked : CountedLocalCaseData.check data frame722 = true := by decide +kernel
theorem case722_fitted : fits case722 = true := by decide +kernel
noncomputable def frame723 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 18, changes := [(167, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (19099, 18553), numericProof := 76445, slack := 0}
noncomputable def case723 : PhysicalCase := ⟨2,169,.west,.push 168 (.stay 167),frame723⟩
theorem frame723_checked : CountedLocalCaseData.check data frame723 = true := by decide +kernel
theorem case723_fitted : fits case723 = true := by decide +kernel
noncomputable def frame724 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 18, changes := [(158, true), (184, false)], beforeBeta := 5439691, beforeBonus := 5832844, afterBeta := 5439691, afterBonus := 5832840, preBeta := 5440906, preBonus := 5834412, restrictionBeforeBeta := 16512, restrictionBeforeBonus := 1340902, restrictionAfterBeta := 941678, restrictionAfterBonus := 1340906, updateProofs := some (19818, 377701), numericProof := 76450, slack := 0}
noncomputable def case724 : PhysicalCase := ⟨2,210,.north,.push 184 (.stay 158),frame724⟩
theorem frame724_checked : CountedLocalCaseData.check data frame724 = true := by decide +kernel
theorem case724_fitted : fits case724 = true := by decide +kernel
noncomputable def frame725 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 18, changes := [(210, true), (184, false)], beforeBeta := 5439693, beforeBonus := 5832841, afterBeta := 5439691, afterBonus := 5832840, preBeta := 5439691, preBonus := 5834415, restrictionBeforeBeta := 2891, restrictionBeforeBonus := 1340913, restrictionAfterBeta := 16512, restrictionAfterBonus := 1340917, updateProofs := some (20869, 377708), numericProof := 76451, slack := 2}
noncomputable def case725 : PhysicalCase := ⟨2,158,.south,.push 184 (.stay 210),frame725⟩
theorem frame725_checked : CountedLocalCaseData.check data frame725 = true := by decide +kernel
theorem case725_fitted : fits case725 = true := by decide +kernel
noncomputable def frame726 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 18, changes := [(159, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832843, afterBeta := 5439691, afterBonus := 5832838, preBeta := 5440930, preBonus := 5834418, restrictionBeforeBeta := 20208, restrictionBeforeBonus := 1340924, restrictionAfterBeta := 943566, restrictionAfterBonus := 1340928, updateProofs := some (21949, 377715), numericProof := 76456, slack := 0}
noncomputable def case726 : PhysicalCase := ⟨2,211,.north,.push 185 (.stay 159),frame726⟩
theorem frame726_checked : CountedLocalCaseData.check data frame726 = true := by decide +kernel
theorem case726_fitted : fits case726 = true := by decide +kernel
noncomputable def frame727 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 18, changes := [(211, true), (185, false)], beforeBeta := 5439694, beforeBonus := 5832842, afterBeta := 5439691, afterBonus := 5832838, preBeta := 5439691, preBonus := 5834421, restrictionBeforeBeta := 19677, restrictionBeforeBonus := 1340932, restrictionAfterBeta := 20208, restrictionAfterBonus := 1340936, updateProofs := some (23648, 377722), numericProof := 76457, slack := 2}
noncomputable def case727 : PhysicalCase := ⟨2,159,.south,.push 185 (.stay 211),frame727⟩
theorem frame727_checked : CountedLocalCaseData.check data frame727 = true := by decide +kernel
theorem case727_fitted : fits case727 = true := by decide +kernel
noncomputable def frame728 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 18, changes := [(186, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832840, afterBeta := 5439691, afterBonus := 5832838, preBeta := 5440955, preBonus := 5834424, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1340943, restrictionAfterBeta := 946126, restrictionAfterBonus := 1340950, updateProofs := some (24871, 377729), numericProof := 76496, slack := 0}
noncomputable def case728 : PhysicalCase := ⟨2,184,.east,.push 185 (.stay 186),frame728⟩
theorem frame728_checked : CountedLocalCaseData.check data frame728 = true := by decide +kernel
theorem case728_fitted : fits case728 = true := by decide +kernel
noncomputable def frame729 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 18, changes := [(184, true), (185, false)], beforeBeta := 5439697, beforeBonus := 5832836, afterBeta := 5439691, afterBonus := 5832838, preBeta := 5439691, preBonus := 5834426, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1340957, restrictionAfterBeta := 79701, restrictionAfterBonus := 1340964, updateProofs := some (25998, 377736), numericProof := 76497, slack := 2}
noncomputable def case729 : PhysicalCase := ⟨2,186,.west,.push 185 (.stay 184),frame729⟩
theorem frame729_checked : CountedLocalCaseData.check data frame729 = true := by decide +kernel
theorem case729_fitted : fits case729 = true := by decide +kernel
noncomputable def frame730 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 18, changes := [(160, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832839, afterBeta := 5439697, afterBonus := 5832836, preBeta := 5440974, preBonus := 5834428, restrictionBeforeBeta := 947685, restrictionBeforeBonus := 1340971, restrictionAfterBeta := 948362, restrictionAfterBonus := 1340975, updateProofs := some (26750, 377743), numericProof := 76502, slack := 0}
noncomputable def case730 : PhysicalCase := ⟨2,212,.north,.push 186 (.stay 160),frame730⟩
theorem frame730_checked : CountedLocalCaseData.check data frame730 = true := by decide +kernel
theorem case730_fitted : fits case730 = true := by decide +kernel
noncomputable def frame731 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 18, changes := [(212, true), (186, false)], beforeBeta := 5439695, beforeBonus := 5832833, afterBeta := 5439697, afterBonus := 5832836, preBeta := 5440026, preBonus := 5834431, restrictionBeforeBeta := 8199, restrictionBeforeBonus := 1340982, restrictionAfterBeta := 949615, restrictionAfterBonus := 1340986, updateProofs := some (27961, 377750), numericProof := 76503, slack := 2}
noncomputable def case731 : PhysicalCase := ⟨2,160,.south,.push 186 (.stay 212),frame731⟩
theorem frame731_checked : CountedLocalCaseData.check data frame731 = true := by decide +kernel
theorem case731_fitted : fits case731 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
