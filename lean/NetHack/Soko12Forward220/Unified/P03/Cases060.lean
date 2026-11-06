import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame720 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 17, changes := [(168, true), (167, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440874, preBonus := 0, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 3, restrictionAfterBeta := 937363, restrictionAfterBonus := 3, updateProofs := some (15015, 14426), numericProof := 77106, slack := 2}
noncomputable def case720 : PhysicalCase := ⟨3,166,.east,.push 167 (.stay 168),frame720⟩
theorem frame720_checked : CountedLocalCaseData.check data frame720 = true := by decide +kernel
theorem case720_fitted : fits case720 = true := by decide +kernel
noncomputable def frame721 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 17, changes := [(166, true), (167, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 14070, restrictionAfterBonus := 3, updateProofs := some (15520, 15016), numericProof := 77107, slack := 0}
noncomputable def case721 : PhysicalCase := ⟨3,168,.west,.push 167 (.stay 166),frame721⟩
theorem frame721_checked : CountedLocalCaseData.check data frame721 = true := by decide +kernel
theorem case721_fitted : fits case721 = true := by decide +kernel
noncomputable def frame722 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 17, changes := [(142, true), (168, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (15994, 15521), numericProof := 77108, slack := 1}
noncomputable def case722 : PhysicalCase := ⟨3,194,.north,.push 168 (.stay 142),frame722⟩
theorem frame722_checked : CountedLocalCaseData.check data frame722 = true := by decide +kernel
theorem case722_fitted : fits case722 = true := by decide +kernel
noncomputable def frame723 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 17, changes := [(194, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (17937, 15995), numericProof := 77109, slack := 1}
noncomputable def case723 : PhysicalCase := ⟨3,142,.south,.push 168 (.stay 194),frame723⟩
theorem frame723_checked : CountedLocalCaseData.check data frame723 = true := by decide +kernel
theorem case723_fitted : fits case723 = true := by decide +kernel
noncomputable def frame724 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 17, changes := [(169, true), (168, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (18552, 17938), numericProof := 77110, slack := 1}
noncomputable def case724 : PhysicalCase := ⟨3,167,.east,.push 168 (.stay 169),frame724⟩
theorem frame724_checked : CountedLocalCaseData.check data frame724 = true := by decide +kernel
theorem case724_fitted : fits case724 = true := by decide +kernel
noncomputable def frame725 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 17, changes := [(167, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (19099, 18553), numericProof := 77111, slack := 0}
noncomputable def case725 : PhysicalCase := ⟨3,169,.west,.push 168 (.stay 167),frame725⟩
theorem frame725_checked : CountedLocalCaseData.check data frame725 = true := by decide +kernel
theorem case725_fitted : fits case725 = true := by decide +kernel
noncomputable def frame726 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 17, changes := [(158, true), (184, false)], beforeBeta := 5439691, beforeBonus := 5832874, afterBeta := 5439691, afterBonus := 5832867, preBeta := 5440906, preBonus := 5834730, restrictionBeforeBeta := 16512, restrictionBeforeBonus := 1342895, restrictionAfterBeta := 941678, restrictionAfterBonus := 1342898, updateProofs := some (19818, 378318), numericProof := 77115, slack := 0}
noncomputable def case726 : PhysicalCase := ⟨3,210,.north,.push 184 (.stay 158),frame726⟩
theorem frame726_checked : CountedLocalCaseData.check data frame726 = true := by decide +kernel
theorem case726_fitted : fits case726 = true := by decide +kernel
noncomputable def frame727 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 17, changes := [(210, true), (184, false)], beforeBeta := 5439693, beforeBonus := 5832863, afterBeta := 5439691, afterBonus := 5832867, preBeta := 5439691, preBonus := 5834733, restrictionBeforeBeta := 2891, restrictionBeforeBonus := 1342902, restrictionAfterBeta := 16512, restrictionAfterBonus := 1342905, updateProofs := some (20869, 378322), numericProof := 77116, slack := 2}
noncomputable def case727 : PhysicalCase := ⟨3,158,.south,.push 184 (.stay 210),frame727⟩
theorem frame727_checked : CountedLocalCaseData.check data frame727 = true := by decide +kernel
theorem case727_fitted : fits case727 = true := by decide +kernel
noncomputable def frame728 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 17, changes := [(159, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832871, afterBeta := 5439691, afterBonus := 5832866, preBeta := 5440930, preBonus := 5834736, restrictionBeforeBeta := 20208, restrictionBeforeBonus := 1342909, restrictionAfterBeta := 943566, restrictionAfterBonus := 1342912, updateProofs := some (21949, 378326), numericProof := 77120, slack := 0}
noncomputable def case728 : PhysicalCase := ⟨3,211,.north,.push 185 (.stay 159),frame728⟩
theorem frame728_checked : CountedLocalCaseData.check data frame728 = true := by decide +kernel
theorem case728_fitted : fits case728 = true := by decide +kernel
noncomputable def frame729 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 17, changes := [(211, true), (185, false)], beforeBeta := 5439694, beforeBonus := 5832862, afterBeta := 5439691, afterBonus := 5832866, preBeta := 5439691, preBonus := 5834739, restrictionBeforeBeta := 19677, restrictionBeforeBonus := 1342915, restrictionAfterBeta := 20208, restrictionAfterBonus := 1342918, updateProofs := some (23648, 378330), numericProof := 77121, slack := 2}
noncomputable def case729 : PhysicalCase := ⟨3,159,.south,.push 185 (.stay 211),frame729⟩
theorem frame729_checked : CountedLocalCaseData.check data frame729 = true := by decide +kernel
theorem case729_fitted : fits case729 = true := by decide +kernel
noncomputable def frame730 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 17, changes := [(186, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832867, afterBeta := 5439691, afterBonus := 5832866, preBeta := 5440955, preBonus := 5834742, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1342922, restrictionAfterBeta := 946126, restrictionAfterBonus := 1342926, updateProofs := some (24871, 378334), numericProof := 77127, slack := 0}
noncomputable def case730 : PhysicalCase := ⟨3,184,.east,.push 185 (.stay 186),frame730⟩
theorem frame730_checked : CountedLocalCaseData.check data frame730 = true := by decide +kernel
theorem case730_fitted : fits case730 = true := by decide +kernel
noncomputable def frame731 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 17, changes := [(184, true), (185, false)], beforeBeta := 5439697, beforeBonus := 5832864, afterBeta := 5439691, afterBonus := 5832866, preBeta := 5439691, preBonus := 5834744, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1342930, restrictionAfterBeta := 79701, restrictionAfterBonus := 1342934, updateProofs := some (25998, 378338), numericProof := 77128, slack := 2}
noncomputable def case731 : PhysicalCase := ⟨3,186,.west,.push 185 (.stay 184),frame731⟩
theorem frame731_checked : CountedLocalCaseData.check data frame731 = true := by decide +kernel
theorem case731_fitted : fits case731 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
