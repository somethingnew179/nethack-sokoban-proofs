import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame732 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 16, changes := [(186, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832896, afterBeta := 5439691, afterBonus := 5832895, preBeta := 5440955, preBonus := 5835028, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1344298, restrictionAfterBeta := 946126, restrictionAfterBonus := 1344301, updateProofs := some (24871, 378709), numericProof := 77675, slack := 0}
noncomputable def case732 : PhysicalCase := ⟨4,184,.east,.push 185 (.stay 186),frame732⟩
theorem frame732_checked : CountedLocalCaseData.check data frame732 = true := by decide +kernel
theorem case732_fitted : fits case732 = true := by decide +kernel
noncomputable def frame733 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 16, changes := [(184, true), (185, false)], beforeBeta := 5439697, beforeBonus := 5832893, afterBeta := 5439691, afterBonus := 5832895, preBeta := 5439691, preBonus := 5835030, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1344304, restrictionAfterBeta := 79701, restrictionAfterBonus := 1344307, updateProofs := some (25998, 378712), numericProof := 77676, slack := 2}
noncomputable def case733 : PhysicalCase := ⟨4,186,.west,.push 185 (.stay 184),frame733⟩
theorem frame733_checked : CountedLocalCaseData.check data frame733 = true := by decide +kernel
theorem case733_fitted : fits case733 = true := by decide +kernel
noncomputable def frame734 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 16, changes := [(160, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832897, afterBeta := 5439697, afterBonus := 5832893, preBeta := 5440974, preBonus := 5835032, restrictionBeforeBeta := 947685, restrictionBeforeBonus := 1344310, restrictionAfterBeta := 948362, restrictionAfterBonus := 1344312, updateProofs := some (26750, 378715), numericProof := 77677, slack := 0}
noncomputable def case734 : PhysicalCase := ⟨4,212,.north,.push 186 (.stay 160),frame734⟩
theorem frame734_checked : CountedLocalCaseData.check data frame734 = true := by decide +kernel
theorem case734_fitted : fits case734 = true := by decide +kernel
noncomputable def frame735 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 16, changes := [(212, true), (186, false)], beforeBeta := 5439695, beforeBonus := 5832887, afterBeta := 5439697, afterBonus := 5832893, preBeta := 5440026, preBonus := 5835034, restrictionBeforeBeta := 8199, restrictionBeforeBonus := 1344315, restrictionAfterBeta := 949615, restrictionAfterBonus := 1344317, updateProofs := some (27961, 378718), numericProof := 77678, slack := 2}
noncomputable def case735 : PhysicalCase := ⟨4,160,.south,.push 186 (.stay 212),frame735⟩
theorem frame735_checked : CountedLocalCaseData.check data frame735 = true := by decide +kernel
theorem case735_fitted : fits case735 = true := by decide +kernel
noncomputable def frame736 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 16, changes := [(187, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832895, afterBeta := 5439697, afterBonus := 5832893, preBeta := 5441000, preBonus := 5835035, restrictionBeforeBeta := 949847, restrictionBeforeBonus := 1344320, restrictionAfterBeta := 951000, restrictionAfterBonus := 1344323, updateProofs := some (28839, 378721), numericProof := 77683, slack := 4}
noncomputable def case736 : PhysicalCase := ⟨4,185,.east,.push 186 (.stay 187),frame736⟩
theorem frame736_checked : CountedLocalCaseData.check data frame736 = true := by decide +kernel
theorem case736_fitted : fits case736 = true := by decide +kernel
noncomputable def frame737 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 16, changes := [(185, true), (186, false)], beforeBeta := 5439698, beforeBonus := 5832894, afterBeta := 5439697, afterBonus := 5832893, preBeta := 5440026, preBonus := 5835037, restrictionBeforeBeta := 951446, restrictionBeforeBonus := 1344325, restrictionAfterBeta := 952128, restrictionAfterBonus := 1344327, updateProofs := some (29636, 378724), numericProof := 77684, slack := 2}
noncomputable def case737 : PhysicalCase := ⟨4,187,.west,.push 186 (.stay 185),frame737⟩
theorem frame737_checked : CountedLocalCaseData.check data frame737 = true := by decide +kernel
theorem case737_fitted : fits case737 = true := by decide +kernel
noncomputable def frame738 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 16, changes := [(161, true), (187, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439698, afterBonus := 5832894, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 952399, restrictionBeforeBonus := 3, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (30444, 378726), numericProof := 77685, slack := 2}
noncomputable def case738 : PhysicalCase := ⟨4,213,.north,.push 187 (.stay 161),frame738⟩
theorem frame738_checked : CountedLocalCaseData.check data frame738 = true := by decide +kernel
theorem case738_fitted : fits case738 = true := by decide +kernel
noncomputable def frame739 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 16, changes := [(213, true), (187, false)], beforeBeta := 5439690, beforeBonus := 5832887, afterBeta := 5439698, afterBonus := 5832894, preBeta := 5439690, preBonus := 5835038, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1344330, restrictionAfterBeta := 7685, restrictionAfterBonus := 1344332, updateProofs := some (31856, 378728), numericProof := 77686, slack := 0}
noncomputable def case739 : PhysicalCase := ⟨4,161,.south,.push 187 (.stay 213),frame739⟩
theorem frame739_checked : CountedLocalCaseData.check data frame739 = true := by decide +kernel
theorem case739_fitted : fits case739 = true := by decide +kernel
noncomputable def frame740 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 16, changes := [(163, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (32294, 31857), numericProof := 77687, slack := 7}
noncomputable def case740 : PhysicalCase := ⟨4,215,.north,.push 189 (.stay 163),frame740⟩
theorem frame740_checked : CountedLocalCaseData.check data frame740 = true := by decide +kernel
theorem case740_fitted : fits case740 = true := by decide +kernel
noncomputable def frame741 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 16, changes := [(215, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (34524, 32295), numericProof := 77688, slack := 0}
noncomputable def case741 : PhysicalCase := ⟨4,163,.south,.push 189 (.stay 215),frame741⟩
theorem frame741_checked : CountedLocalCaseData.check data frame741 = true := by decide +kernel
theorem case741_fitted : fits case741 = true := by decide +kernel
noncomputable def frame742 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 16, changes := [(164, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (35000, 34525), numericProof := 77689, slack := 6}
noncomputable def case742 : PhysicalCase := ⟨4,216,.north,.push 190 (.stay 164),frame742⟩
theorem frame742_checked : CountedLocalCaseData.check data frame742 = true := by decide +kernel
theorem case742_fitted : fits case742 = true := by decide +kernel
noncomputable def frame743 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 16, changes := [(216, true), (190, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (37936, 35001), numericProof := 77690, slack := 2}
noncomputable def case743 : PhysicalCase := ⟨4,164,.south,.push 190 (.stay 216),frame743⟩
theorem frame743_checked : CountedLocalCaseData.check data frame743 = true := by decide +kernel
theorem case743_fitted : fits case743 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
