import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame720 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 20, changes := [(158, true), (184, false)], beforeBeta := 5439691, beforeBonus := 5832766, afterBeta := 5439691, afterBonus := 5832757, preBeta := 5440906, preBonus := 5833359, restrictionBeforeBeta := 16512, restrictionBeforeBonus := 941677, restrictionAfterBeta := 941678, restrictionAfterBonus := 942088, updateProofs := some (19818, 19759), numericProof := 26135, slack := 0}
noncomputable def case720 : PhysicalCase := ⟨0,210,.north,.push 184 (.stay 158),frame720⟩
theorem frame720_checked : CountedLocalCaseData.check data frame720 = true := by decide +kernel
theorem case720_fitted : fits case720 = true := by decide +kernel
noncomputable def frame721 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 20, changes := [(210, true), (184, false)], beforeBeta := 5439693, beforeBonus := 5832762, afterBeta := 5439691, afterBonus := 5832757, preBeta := 5439691, preBonus := 5833362, restrictionBeforeBeta := 2891, restrictionBeforeBonus := 942676, restrictionAfterBeta := 16512, restrictionAfterBonus := 943046, updateProofs := some (20869, 20795), numericProof := 26136, slack := 2}
noncomputable def case721 : PhysicalCase := ⟨0,158,.south,.push 184 (.stay 210),frame721⟩
theorem frame721_checked : CountedLocalCaseData.check data frame721 = true := by decide +kernel
theorem case721_fitted : fits case721 = true := by decide +kernel
noncomputable def frame722 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 20, changes := [(159, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832768, afterBeta := 5439691, afterBonus := 5832748, preBeta := 5440930, preBonus := 5833365, restrictionBeforeBeta := 20208, restrictionBeforeBonus := 943565, restrictionAfterBeta := 943566, restrictionAfterBonus := 944296, updateProofs := some (21949, 21888), numericProof := 26880, slack := 0}
noncomputable def case722 : PhysicalCase := ⟨0,211,.north,.push 185 (.stay 159),frame722⟩
theorem frame722_checked : CountedLocalCaseData.check data frame722 = true := by decide +kernel
theorem case722_fitted : fits case722 = true := by decide +kernel
noncomputable def frame723 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 20, changes := [(211, true), (185, false)], beforeBeta := 5439694, beforeBonus := 5832756, afterBeta := 5439691, afterBonus := 5832748, preBeta := 5439691, preBonus := 5833368, restrictionBeforeBeta := 19677, restrictionBeforeBonus := 944976, restrictionAfterBeta := 20208, restrictionAfterBonus := 945403, updateProofs := some (23648, 23574), numericProof := 26881, slack := 2}
noncomputable def case723 : PhysicalCase := ⟨0,159,.south,.push 185 (.stay 211),frame723⟩
theorem frame723_checked : CountedLocalCaseData.check data frame723 = true := by decide +kernel
theorem case723_fitted : fits case723 = true := by decide +kernel
noncomputable def frame724 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 20, changes := [(186, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832757, afterBeta := 5439691, afterBonus := 5832748, preBeta := 5440955, preBonus := 5833371, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 946125, restrictionAfterBeta := 946126, restrictionAfterBonus := 946762, updateProofs := some (24871, 24806), numericProof := 27496, slack := 0}
noncomputable def case724 : PhysicalCase := ⟨0,184,.east,.push 185 (.stay 186),frame724⟩
theorem frame724_checked : CountedLocalCaseData.check data frame724 = true := by decide +kernel
theorem case724_fitted : fits case724 = true := by decide +kernel
noncomputable def frame725 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 20, changes := [(184, true), (185, false)], beforeBeta := 5439697, beforeBonus := 5832745, afterBeta := 5439691, afterBonus := 5832748, preBeta := 5439691, preBonus := 5833373, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 947197, restrictionAfterBeta := 79701, restrictionAfterBonus := 947637, updateProofs := some (25998, 25935), numericProof := 27497, slack := 2}
noncomputable def case725 : PhysicalCase := ⟨0,186,.west,.push 185 (.stay 184),frame725⟩
theorem frame725_checked : CountedLocalCaseData.check data frame725 = true := by decide +kernel
theorem case725_fitted : fits case725 = true := by decide +kernel
noncomputable def frame726 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 20, changes := [(160, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832744, afterBeta := 5439697, afterBonus := 5832745, preBeta := 5440974, preBonus := 5833376, restrictionBeforeBeta := 947685, restrictionBeforeBonus := 948361, restrictionAfterBeta := 948362, restrictionAfterBonus := 948847, updateProofs := some (26750, 26701), numericProof := 27917, slack := 0}
noncomputable def case726 : PhysicalCase := ⟨0,212,.north,.push 186 (.stay 160),frame726⟩
theorem frame726_checked : CountedLocalCaseData.check data frame726 = true := by decide +kernel
theorem case726_fitted : fits case726 = true := by decide +kernel
noncomputable def frame727 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 20, changes := [(212, true), (186, false)], beforeBeta := 5439695, beforeBonus := 5832747, afterBeta := 5439697, afterBonus := 5832745, preBeta := 5440026, preBonus := 5833379, restrictionBeforeBeta := 8199, restrictionBeforeBonus := 949590, restrictionAfterBeta := 949615, restrictionAfterBonus := 949793, updateProofs := some (27961, 27903), numericProof := 27918, slack := 2}
noncomputable def case727 : PhysicalCase := ⟨0,160,.south,.push 186 (.stay 212),frame727⟩
theorem frame727_checked : CountedLocalCaseData.check data frame727 = true := by decide +kernel
theorem case727_fitted : fits case727 = true := by decide +kernel
noncomputable def frame728 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 20, changes := [(187, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832748, afterBeta := 5439697, afterBonus := 5832745, preBeta := 5441000, preBonus := 5833382, restrictionBeforeBeta := 949847, restrictionBeforeBonus := 950999, restrictionAfterBeta := 951000, restrictionAfterBonus := 951429, updateProofs := some (28839, 28790), numericProof := 28158, slack := 4}
noncomputable def case728 : PhysicalCase := ⟨0,185,.east,.push 186 (.stay 187),frame728⟩
theorem frame728_checked : CountedLocalCaseData.check data frame728 = true := by decide +kernel
theorem case728_fitted : fits case728 = true := by decide +kernel
noncomputable def frame729 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 20, changes := [(185, true), (186, false)], beforeBeta := 5439698, beforeBonus := 5832739, afterBeta := 5439697, afterBonus := 5832745, preBeta := 5440026, preBonus := 5833385, restrictionBeforeBeta := 951446, restrictionBeforeBonus := 952107, restrictionAfterBeta := 952128, restrictionAfterBonus := 952352, updateProofs := some (29636, 29587), numericProof := 28627, slack := 2}
noncomputable def case729 : PhysicalCase := ⟨0,187,.west,.push 186 (.stay 185),frame729⟩
theorem frame729_checked : CountedLocalCaseData.check data frame729 = true := by decide +kernel
theorem case729_fitted : fits case729 = true := by decide +kernel
noncomputable def frame730 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 20, changes := [(161, true), (187, false)], beforeBeta := 5439691, beforeBonus := 5832738, afterBeta := 5439698, afterBonus := 5832739, preBeta := 5439690, preBonus := 5833388, restrictionBeforeBeta := 952399, restrictionBeforeBonus := 953066, restrictionAfterBeta := 7685, restrictionAfterBonus := 953546, updateProofs := some (30444, 30409), numericProof := 28836, slack := 2}
noncomputable def case730 : PhysicalCase := ⟨0,213,.north,.push 187 (.stay 161),frame730⟩
theorem frame730_checked : CountedLocalCaseData.check data frame730 = true := by decide +kernel
theorem case730_fitted : fits case730 = true := by decide +kernel
noncomputable def frame731 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 20, changes := [(213, true), (187, false)], beforeBeta := 5439690, beforeBonus := 5832753, afterBeta := 5439698, afterBonus := 5832739, preBeta := 5439690, preBonus := 5833391, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 954561, restrictionAfterBeta := 7685, restrictionAfterBonus := 954797, updateProofs := some (31856, 31812), numericProof := 28953, slack := 0}
noncomputable def case731 : PhysicalCase := ⟨0,161,.south,.push 187 (.stay 213),frame731⟩
theorem frame731_checked : CountedLocalCaseData.check data frame731 = true := by decide +kernel
theorem case731_fitted : fits case731 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
