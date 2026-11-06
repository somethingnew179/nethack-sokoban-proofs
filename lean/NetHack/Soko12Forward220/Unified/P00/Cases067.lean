import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame804 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 20, changes := [(264, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832764, preBeta := 5439691, preBonus := 5833549, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1144355, restrictionAfterBeta := 8531, restrictionAfterBonus := 1145507, updateProofs := some (191021, 190947), numericProof := 65678, slack := 0}
noncomputable def case804 : PhysicalCase := ⟨0,262,.east,.push 263 (.stay 264),frame804⟩
theorem frame804_checked : CountedLocalCaseData.check data frame804 = true := by decide +kernel
theorem case804_fitted : fits case804 = true := by decide +kernel
noncomputable def frame805 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 20, changes := [(262, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832749, afterBeta := 5439691, afterBonus := 5832764, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1147148, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (192504, 192430), numericProof := 65679, slack := 2}
noncomputable def case805 : PhysicalCase := ⟨0,264,.west,.push 263 (.stay 262),frame805⟩
theorem frame805_checked : CountedLocalCaseData.check data frame805 = true := by decide +kernel
theorem case805_fitted : fits case805 = true := by decide +kernel
noncomputable def frame806 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 20, changes := [(238, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832749, preBeta := 5439691, preBonus := 5833553, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1148569, restrictionAfterBeta := 8531, restrictionAfterBonus := 1150118, updateProofs := some (194360, 194286), numericProof := 66132, slack := 0}
noncomputable def case806 : PhysicalCase := ⟨0,290,.north,.push 264 (.stay 238),frame806⟩
theorem frame806_checked : CountedLocalCaseData.check data frame806 = true := by decide +kernel
theorem case806_fitted : fits case806 = true := by decide +kernel
noncomputable def frame807 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 20, changes := [(290, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832758, afterBeta := 5439691, afterBonus := 5832749, preBeta := 5439691, preBonus := 5833556, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1150730, restrictionAfterBeta := 8531, restrictionAfterBonus := 1151450, updateProofs := some (196259, 196182), numericProof := 66133, slack := 4}
noncomputable def case807 : PhysicalCase := ⟨0,238,.south,.push 264 (.stay 290),frame807⟩
theorem frame807_checked : CountedLocalCaseData.check data frame807 = true := by decide +kernel
theorem case807_fitted : fits case807 = true := by decide +kernel
noncomputable def frame808 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 20, changes := [(265, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832764, afterBeta := 5439691, afterBonus := 5832749, preBeta := 5439691, preBonus := 5833559, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1152870, restrictionAfterBeta := 8531, restrictionAfterBonus := 1153578, updateProofs := some (198116, 198042), numericProof := 66134, slack := 2}
noncomputable def case808 : PhysicalCase := ⟨0,263,.east,.push 264 (.stay 265),frame808⟩
theorem frame808_checked : CountedLocalCaseData.check data frame808 = true := by decide +kernel
theorem case808_fitted : fits case808 = true := by decide +kernel
noncomputable def frame809 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 20, changes := [(263, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832746, afterBeta := 5439691, afterBonus := 5832749, preBeta := 5439691, preBonus := 5833562, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1155411, restrictionAfterBeta := 8531, restrictionAfterBonus := 1156916, updateProofs := some (199972, 199898), numericProof := 66135, slack := 2}
noncomputable def case809 : PhysicalCase := ⟨0,265,.west,.push 264 (.stay 263),frame809⟩
theorem frame809_checked : CountedLocalCaseData.check data frame809 = true := by decide +kernel
theorem case809_fitted : fits case809 = true := by decide +kernel
noncomputable def frame810 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 20, changes := [(239, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832743, afterBeta := 5439691, afterBonus := 5832746, preBeta := 5439691, preBonus := 5833565, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1158480, restrictionAfterBeta := 8531, restrictionAfterBonus := 1159906, updateProofs := some (201896, 201822), numericProof := 66618, slack := 0}
noncomputable def case810 : PhysicalCase := ⟨0,291,.north,.push 265 (.stay 239),frame810⟩
theorem frame810_checked : CountedLocalCaseData.check data frame810 = true := by decide +kernel
theorem case810_fitted : fits case810 = true := by decide +kernel
noncomputable def frame811 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 20, changes := [(291, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832740, afterBeta := 5439691, afterBonus := 5832746, preBeta := 5439691, preBonus := 5833568, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1162237, restrictionAfterBeta := 8531, restrictionAfterBonus := 1162642, updateProofs := some (203881, 203804), numericProof := 67042, slack := 2}
noncomputable def case811 : PhysicalCase := ⟨0,239,.south,.push 265 (.stay 291),frame811⟩
theorem frame811_checked : CountedLocalCaseData.check data frame811 = true := by decide +kernel
theorem case811_fitted : fits case811 = true := by decide +kernel
noncomputable def frame812 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 20, changes := [(244, true), (270, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 5833571, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1167219, restrictionAfterBeta := 8531, restrictionAfterBonus := 1167997, updateProofs := some (208395, 208321), numericProof := 67043, slack := 0}
noncomputable def case812 : PhysicalCase := ⟨0,296,.north,.push 270 (.stay 244),frame812⟩
theorem frame812_checked : CountedLocalCaseData.check data frame812 = true := by decide +kernel
theorem case812_fitted : fits case812 = true := by decide +kernel
noncomputable def frame813 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 20, changes := [(296, true), (270, false)], beforeBeta := 5439691, beforeBonus := 5832714, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1169117, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (213190, 213113), numericProof := 67044, slack := 1}
noncomputable def case813 : PhysicalCase := ⟨0,244,.south,.push 270 (.stay 296),frame813⟩
theorem frame813_checked : CountedLocalCaseData.check data frame813 = true := by decide +kernel
theorem case813_fitted : fits case813 = true := by decide +kernel
noncomputable def frame814 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 20, changes := [(245, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832712, afterBeta := 5439701, afterBonus := 5832713, preBeta := 5439687, preBonus := 5833573, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1173751, restrictionAfterBeta := 829, restrictionAfterBonus := 1175411, updateProofs := some (215711, 215621), numericProof := 69793, slack := 1}
noncomputable def case814 : PhysicalCase := ⟨0,297,.north,.push 271 (.stay 245),frame814⟩
theorem frame814_checked : CountedLocalCaseData.check data frame814 = true := by decide +kernel
theorem case814_fitted : fits case814 = true := by decide +kernel
noncomputable def frame815 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 20, changes := [(297, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832715, afterBeta := 5439701, afterBonus := 5832713, preBeta := 5439687, preBonus := 5833576, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1178291, restrictionAfterBeta := 829, restrictionAfterBonus := 1179940, updateProofs := some (218426, 218336), numericProof := 70545, slack := 1}
noncomputable def case815 : PhysicalCase := ⟨0,245,.south,.push 271 (.stay 297),frame815⟩
theorem frame815_checked : CountedLocalCaseData.check data frame815 = true := by decide +kernel
theorem case815_fitted : fits case815 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
