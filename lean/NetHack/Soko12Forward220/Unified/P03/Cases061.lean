import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame732 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 17, changes := [(160, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832870, afterBeta := 5439697, afterBonus := 5832864, preBeta := 5440974, preBonus := 5834746, restrictionBeforeBeta := 947685, restrictionBeforeBonus := 1342938, restrictionAfterBeta := 948362, restrictionAfterBonus := 1342941, updateProofs := some (26750, 378342), numericProof := 77132, slack := 0}
noncomputable def case732 : PhysicalCase := ⟨3,212,.north,.push 186 (.stay 160),frame732⟩
theorem frame732_checked : CountedLocalCaseData.check data frame732 = true := by decide +kernel
theorem case732_fitted : fits case732 = true := by decide +kernel
noncomputable def frame733 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 17, changes := [(212, true), (186, false)], beforeBeta := 5439695, beforeBonus := 5832861, afterBeta := 5439697, afterBonus := 5832864, preBeta := 5440026, preBonus := 5834749, restrictionBeforeBeta := 8199, restrictionBeforeBonus := 1342945, restrictionAfterBeta := 949615, restrictionAfterBonus := 1342948, updateProofs := some (27961, 378346), numericProof := 77133, slack := 2}
noncomputable def case733 : PhysicalCase := ⟨3,160,.south,.push 186 (.stay 212),frame733⟩
theorem frame733_checked : CountedLocalCaseData.check data frame733 = true := by decide +kernel
theorem case733_fitted : fits case733 = true := by decide +kernel
noncomputable def frame734 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 17, changes := [(187, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832866, afterBeta := 5439697, afterBonus := 5832864, preBeta := 5441000, preBonus := 5834752, restrictionBeforeBeta := 949847, restrictionBeforeBonus := 1342952, restrictionAfterBeta := 951000, restrictionAfterBonus := 1342956, updateProofs := some (28839, 378350), numericProof := 77139, slack := 4}
noncomputable def case734 : PhysicalCase := ⟨3,185,.east,.push 186 (.stay 187),frame734⟩
theorem frame734_checked : CountedLocalCaseData.check data frame734 = true := by decide +kernel
theorem case734_fitted : fits case734 = true := by decide +kernel
noncomputable def frame735 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 17, changes := [(185, true), (186, false)], beforeBeta := 5439698, beforeBonus := 5832865, afterBeta := 5439697, afterBonus := 5832864, preBeta := 5440026, preBonus := 5834754, restrictionBeforeBeta := 951446, restrictionBeforeBonus := 1342959, restrictionAfterBeta := 952128, restrictionAfterBonus := 1342962, updateProofs := some (29636, 378354), numericProof := 77140, slack := 2}
noncomputable def case735 : PhysicalCase := ⟨3,187,.west,.push 186 (.stay 185),frame735⟩
theorem frame735_checked : CountedLocalCaseData.check data frame735 = true := by decide +kernel
theorem case735_fitted : fits case735 = true := by decide +kernel
noncomputable def frame736 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 17, changes := [(161, true), (187, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439698, afterBonus := 5832865, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 952399, restrictionBeforeBonus := 3, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (30444, 378357), numericProof := 77141, slack := 2}
noncomputable def case736 : PhysicalCase := ⟨3,213,.north,.push 187 (.stay 161),frame736⟩
theorem frame736_checked : CountedLocalCaseData.check data frame736 = true := by decide +kernel
theorem case736_fitted : fits case736 = true := by decide +kernel
noncomputable def frame737 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 17, changes := [(213, true), (187, false)], beforeBeta := 5439690, beforeBonus := 5832859, afterBeta := 5439698, afterBonus := 5832865, preBeta := 5439690, preBonus := 5834755, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1342966, restrictionAfterBeta := 7685, restrictionAfterBonus := 1342969, updateProofs := some (31856, 378360), numericProof := 77142, slack := 0}
noncomputable def case737 : PhysicalCase := ⟨3,161,.south,.push 187 (.stay 213),frame737⟩
theorem frame737_checked : CountedLocalCaseData.check data frame737 = true := by decide +kernel
theorem case737_fitted : fits case737 = true := by decide +kernel
noncomputable def frame738 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 17, changes := [(163, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (32294, 31857), numericProof := 77143, slack := 7}
noncomputable def case738 : PhysicalCase := ⟨3,215,.north,.push 189 (.stay 163),frame738⟩
theorem frame738_checked : CountedLocalCaseData.check data frame738 = true := by decide +kernel
theorem case738_fitted : fits case738 = true := by decide +kernel
noncomputable def frame739 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 17, changes := [(215, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (34524, 32295), numericProof := 77144, slack := 0}
noncomputable def case739 : PhysicalCase := ⟨3,163,.south,.push 189 (.stay 215),frame739⟩
theorem frame739_checked : CountedLocalCaseData.check data frame739 = true := by decide +kernel
theorem case739_fitted : fits case739 = true := by decide +kernel
noncomputable def frame740 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 17, changes := [(164, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (35000, 34525), numericProof := 77145, slack := 6}
noncomputable def case740 : PhysicalCase := ⟨3,216,.north,.push 190 (.stay 164),frame740⟩
theorem frame740_checked : CountedLocalCaseData.check data frame740 = true := by decide +kernel
theorem case740_fitted : fits case740 = true := by decide +kernel
noncomputable def frame741 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 17, changes := [(216, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (37936, 35001), numericProof := 77146, slack := 2}
noncomputable def case741 : PhysicalCase := ⟨3,164,.south,.push 190 (.stay 216),frame741⟩
theorem frame741_checked : CountedLocalCaseData.check data frame741 = true := by decide +kernel
theorem case741_fitted : fits case741 = true := by decide +kernel
noncomputable def frame742 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 17, changes := [(191, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (39482, 37937), numericProof := 77147, slack := 2}
noncomputable def case742 : PhysicalCase := ⟨3,189,.east,.push 190 (.stay 191),frame742⟩
theorem frame742_checked : CountedLocalCaseData.check data frame742 = true := by decide +kernel
theorem case742_fitted : fits case742 = true := by decide +kernel
noncomputable def frame743 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 17, changes := [(189, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (40870, 39483), numericProof := 77148, slack := 0}
noncomputable def case743 : PhysicalCase := ⟨3,191,.west,.push 190 (.stay 189),frame743⟩
theorem frame743_checked : CountedLocalCaseData.check data frame743 = true := by decide +kernel
theorem case743_fitted : fits case743 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
