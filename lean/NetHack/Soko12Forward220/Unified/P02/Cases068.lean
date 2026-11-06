import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame816 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 18, changes := [(244, true), (270, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (208395, 203882), numericProof := 76654, slack := 0}
noncomputable def case816 : PhysicalCase := ⟨2,296,.north,.push 270 (.stay 244),frame816⟩
theorem frame816_checked : CountedLocalCaseData.check data frame816 = true := by decide +kernel
theorem case816_fitted : fits case816 = true := by decide +kernel
noncomputable def frame817 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 18, changes := [(296, true), (270, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (213190, 208396), numericProof := 76655, slack := 1}
noncomputable def case817 : PhysicalCase := ⟨2,244,.south,.push 270 (.stay 296),frame817⟩
theorem frame817_checked : CountedLocalCaseData.check data frame817 = true := by decide +kernel
theorem case817_fitted : fits case817 = true := by decide +kernel
noncomputable def frame818 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 18, changes := [(245, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (215711, 213191), numericProof := 76656, slack := 1}
noncomputable def case818 : PhysicalCase := ⟨2,297,.north,.push 271 (.stay 245),frame818⟩
theorem frame818_checked : CountedLocalCaseData.check data frame818 = true := by decide +kernel
theorem case818_fitted : fits case818 = true := by decide +kernel
noncomputable def frame819 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 18, changes := [(297, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (218426, 215712), numericProof := 76656, slack := 1}
noncomputable def case819 : PhysicalCase := ⟨2,245,.south,.push 271 (.stay 297),frame819⟩
theorem frame819_checked : CountedLocalCaseData.check data frame819 = true := by decide +kernel
theorem case819_fitted : fits case819 = true := by decide +kernel
noncomputable def frame820 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 18, changes := [(272, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (221039, 218427), numericProof := 76657, slack := 1}
noncomputable def case820 : PhysicalCase := ⟨2,270,.east,.push 271 (.stay 272),frame820⟩
theorem frame820_checked : CountedLocalCaseData.check data frame820 = true := by decide +kernel
theorem case820_fitted : fits case820 = true := by decide +kernel
noncomputable def frame821 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 18, changes := [(270, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (223611, 221040), numericProof := 76657, slack := 1}
noncomputable def case821 : PhysicalCase := ⟨2,272,.west,.push 271 (.stay 270),frame821⟩
theorem frame821_checked : CountedLocalCaseData.check data frame821 = true := by decide +kernel
theorem case821_fitted : fits case821 = true := by decide +kernel
noncomputable def frame822 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 18, changes := [(290, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341373, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (225168, 378017), numericProof := 76658, slack := 0}
noncomputable def case822 : PhysicalCase := ⟨2,288,.east,.push 289 (.stay 290),frame822⟩
theorem frame822_checked : CountedLocalCaseData.check data frame822 = true := by decide +kernel
theorem case822_fitted : fits case822 = true := by decide +kernel
noncomputable def frame823 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 18, changes := [(288, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341373, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (226719, 378024), numericProof := 76659, slack := 5}
noncomputable def case823 : PhysicalCase := ⟨2,290,.west,.push 289 (.stay 288),frame823⟩
theorem frame823_checked : CountedLocalCaseData.check data frame823 = true := by decide +kernel
theorem case823_fitted : fits case823 = true := by decide +kernel
noncomputable def frame824 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 18, changes := [(291, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341380, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (228281, 378031), numericProof := 76660, slack := 0}
noncomputable def case824 : PhysicalCase := ⟨2,289,.east,.push 290 (.stay 291),frame824⟩
theorem frame824_checked : CountedLocalCaseData.check data frame824 = true := by decide +kernel
theorem case824_fitted : fits case824 = true := by decide +kernel
noncomputable def frame825 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 18, changes := [(289, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341380, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (229835, 378038), numericProof := 76661, slack := 2}
noncomputable def case825 : PhysicalCase := ⟨2,291,.west,.push 290 (.stay 289),frame825⟩
theorem frame825_checked : CountedLocalCaseData.check data frame825 = true := by decide +kernel
theorem case825_fitted : fits case825 = true := by decide +kernel
noncomputable def frame826 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 18, changes := [(265, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 5834505, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341387, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341394, updateProofs := some (231551, 378045), numericProof := 76662, slack := 0}
noncomputable def case826 : PhysicalCase := ⟨2,317,.north,.push 291 (.stay 265),frame826⟩
theorem frame826_checked : CountedLocalCaseData.check data frame826 = true := by decide +kernel
theorem case826_fitted : fits case826 = true := by decide +kernel
noncomputable def frame827 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 18, changes := [(317, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832849, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341401, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (233281, 378052), numericProof := 76663, slack := 7}
noncomputable def case827 : PhysicalCase := ⟨2,265,.south,.push 291 (.stay 317),frame827⟩
theorem frame827_checked : CountedLocalCaseData.check data frame827 = true := by decide +kernel
theorem case827_fitted : fits case827 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
