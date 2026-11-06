import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame732 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 18, changes := [(187, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832838, afterBeta := 5439697, afterBonus := 5832836, preBeta := 5441000, preBonus := 5834434, restrictionBeforeBeta := 949847, restrictionBeforeBonus := 1340993, restrictionAfterBeta := 951000, restrictionAfterBonus := 1341000, updateProofs := some (28839, 377757), numericProof := 76543, slack := 4}
noncomputable def case732 : PhysicalCase := ⟨2,185,.east,.push 186 (.stay 187),frame732⟩
theorem frame732_checked : CountedLocalCaseData.check data frame732 = true := by decide +kernel
theorem case732_fitted : fits case732 = true := by decide +kernel
noncomputable def frame733 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 18, changes := [(185, true), (186, false)], beforeBeta := 5439698, beforeBonus := 5832837, afterBeta := 5439697, afterBonus := 5832836, preBeta := 5440026, preBonus := 5834436, restrictionBeforeBeta := 951446, restrictionBeforeBonus := 1341004, restrictionAfterBeta := 952128, restrictionAfterBonus := 1341008, updateProofs := some (29636, 377764), numericProof := 76544, slack := 2}
noncomputable def case733 : PhysicalCase := ⟨2,187,.west,.push 186 (.stay 185),frame733⟩
theorem frame733_checked : CountedLocalCaseData.check data frame733 = true := by decide +kernel
theorem case733_fitted : fits case733 = true := by decide +kernel
noncomputable def frame734 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 18, changes := [(161, true), (187, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439698, afterBonus := 5832837, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 952399, restrictionBeforeBonus := 3, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (30444, 377768), numericProof := 76545, slack := 2}
noncomputable def case734 : PhysicalCase := ⟨2,213,.north,.push 187 (.stay 161),frame734⟩
theorem frame734_checked : CountedLocalCaseData.check data frame734 = true := by decide +kernel
theorem case734_fitted : fits case734 = true := by decide +kernel
noncomputable def frame735 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 18, changes := [(213, true), (187, false)], beforeBeta := 5439690, beforeBonus := 5832831, afterBeta := 5439698, afterBonus := 5832837, preBeta := 5439690, preBonus := 5834437, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1341015, restrictionAfterBeta := 7685, restrictionAfterBonus := 1341019, updateProofs := some (31856, 377772), numericProof := 76546, slack := 0}
noncomputable def case735 : PhysicalCase := ⟨2,161,.south,.push 187 (.stay 213),frame735⟩
theorem frame735_checked : CountedLocalCaseData.check data frame735 = true := by decide +kernel
theorem case735_fitted : fits case735 = true := by decide +kernel
noncomputable def frame736 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 18, changes := [(163, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (32294, 31857), numericProof := 76547, slack := 7}
noncomputable def case736 : PhysicalCase := ⟨2,215,.north,.push 189 (.stay 163),frame736⟩
theorem frame736_checked : CountedLocalCaseData.check data frame736 = true := by decide +kernel
theorem case736_fitted : fits case736 = true := by decide +kernel
noncomputable def frame737 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 18, changes := [(215, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (34524, 32295), numericProof := 76548, slack := 0}
noncomputable def case737 : PhysicalCase := ⟨2,163,.south,.push 189 (.stay 215),frame737⟩
theorem frame737_checked : CountedLocalCaseData.check data frame737 = true := by decide +kernel
theorem case737_fitted : fits case737 = true := by decide +kernel
noncomputable def frame738 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 18, changes := [(164, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (35000, 34525), numericProof := 76549, slack := 6}
noncomputable def case738 : PhysicalCase := ⟨2,216,.north,.push 190 (.stay 164),frame738⟩
theorem frame738_checked : CountedLocalCaseData.check data frame738 = true := by decide +kernel
theorem case738_fitted : fits case738 = true := by decide +kernel
noncomputable def frame739 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 18, changes := [(216, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (37936, 35001), numericProof := 76550, slack := 2}
noncomputable def case739 : PhysicalCase := ⟨2,164,.south,.push 190 (.stay 216),frame739⟩
theorem frame739_checked : CountedLocalCaseData.check data frame739 = true := by decide +kernel
theorem case739_fitted : fits case739 = true := by decide +kernel
noncomputable def frame740 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 18, changes := [(191, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (39482, 37937), numericProof := 76551, slack := 2}
noncomputable def case740 : PhysicalCase := ⟨2,189,.east,.push 190 (.stay 191),frame740⟩
theorem frame740_checked : CountedLocalCaseData.check data frame740 = true := by decide +kernel
theorem case740_fitted : fits case740 = true := by decide +kernel
noncomputable def frame741 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 18, changes := [(189, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (40870, 39483), numericProof := 76552, slack := 0}
noncomputable def case741 : PhysicalCase := ⟨2,191,.west,.push 190 (.stay 189),frame741⟩
theorem frame741_checked : CountedLocalCaseData.check data frame741 = true := by decide +kernel
theorem case741_fitted : fits case741 = true := by decide +kernel
noncomputable def frame742 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 18, changes := [(192, true), (191, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (42814, 40871), numericProof := 76553, slack := 2}
noncomputable def case742 : PhysicalCase := ⟨2,190,.east,.push 191 (.stay 192),frame742⟩
theorem frame742_checked : CountedLocalCaseData.check data frame742 = true := by decide +kernel
theorem case742_fitted : fits case742 = true := by decide +kernel
noncomputable def frame743 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 18, changes := [(190, true), (191, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (44466, 42815), numericProof := 76554, slack := 0}
noncomputable def case743 : PhysicalCase := ⟨2,192,.west,.push 191 (.stay 190),frame743⟩
theorem frame743_checked : CountedLocalCaseData.check data frame743 = true := by decide +kernel
theorem case743_fitted : fits case743 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
