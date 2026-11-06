import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame816 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 19, changes := [(245, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832814, afterBeta := 5439701, afterBonus := 5832809, preBeta := 5439687, preBonus := 5834161, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1338143, restrictionAfterBeta := 829, restrictionAfterBonus := 1338145, updateProofs := some (215711, 376935), numericProof := 75876, slack := 1}
noncomputable def case816 : PhysicalCase := ⟨1,297,.north,.push 271 (.stay 245),frame816⟩
theorem frame816_checked : CountedLocalCaseData.check data frame816 = true := by decide +kernel
theorem case816_fitted : fits case816 = true := by decide +kernel
noncomputable def frame817 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 19, changes := [(297, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832806, afterBeta := 5439701, afterBonus := 5832809, preBeta := 5439687, preBonus := 5834164, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1338147, restrictionAfterBeta := 829, restrictionAfterBonus := 1338149, updateProofs := some (218426, 376937), numericProof := 75876, slack := 1}
noncomputable def case817 : PhysicalCase := ⟨1,245,.south,.push 271 (.stay 297),frame817⟩
theorem frame817_checked : CountedLocalCaseData.check data frame817 = true := by decide +kernel
theorem case817_fitted : fits case817 = true := by decide +kernel
noncomputable def frame818 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 19, changes := [(272, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439701, afterBonus := 5832809, preBeta := 5439687, preBonus := 5834165, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1338151, restrictionAfterBeta := 829, restrictionAfterBonus := 1338153, updateProofs := some (221039, 376939), numericProof := 75880, slack := 1}
noncomputable def case818 : PhysicalCase := ⟨1,270,.east,.push 271 (.stay 272),frame818⟩
theorem frame818_checked : CountedLocalCaseData.check data frame818 = true := by decide +kernel
theorem case818_fitted : fits case818 = true := by decide +kernel
noncomputable def frame819 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 19, changes := [(270, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832810, afterBeta := 5439701, afterBonus := 5832809, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1338155, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (223611, 376941), numericProof := 75881, slack := 1}
noncomputable def case819 : PhysicalCase := ⟨1,272,.west,.push 271 (.stay 270),frame819⟩
theorem frame819_checked : CountedLocalCaseData.check data frame819 = true := by decide +kernel
theorem case819_fitted : fits case819 = true := by decide +kernel
noncomputable def frame820 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 19, changes := [(290, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338176, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (225168, 376962), numericProof := 75882, slack := 0}
noncomputable def case820 : PhysicalCase := ⟨1,288,.east,.push 289 (.stay 290),frame820⟩
theorem frame820_checked : CountedLocalCaseData.check data frame820 = true := by decide +kernel
theorem case820_fitted : fits case820 = true := by decide +kernel
noncomputable def frame821 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 19, changes := [(288, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338176, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (226719, 376983), numericProof := 75883, slack := 5}
noncomputable def case821 : PhysicalCase := ⟨1,290,.west,.push 289 (.stay 288),frame821⟩
theorem frame821_checked : CountedLocalCaseData.check data frame821 = true := by decide +kernel
theorem case821_fitted : fits case821 = true := by decide +kernel
noncomputable def frame822 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 19, changes := [(291, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 5834168, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338197, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338199, updateProofs := some (228281, 377004), numericProof := 75884, slack := 0}
noncomputable def case822 : PhysicalCase := ⟨1,289,.east,.push 290 (.stay 291),frame822⟩
theorem frame822_checked : CountedLocalCaseData.check data frame822 = true := by decide +kernel
theorem case822_fitted : fits case822 = true := by decide +kernel
noncomputable def frame823 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 19, changes := [(289, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832817, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338201, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (229835, 377025), numericProof := 75885, slack := 2}
noncomputable def case823 : PhysicalCase := ⟨1,291,.west,.push 290 (.stay 289),frame823⟩
theorem frame823_checked : CountedLocalCaseData.check data frame823 = true := by decide +kernel
theorem case823_fitted : fits case823 = true := by decide +kernel
noncomputable def frame824 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 19, changes := [(265, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832817, afterBeta := 5439691, afterBonus := 5832817, preBeta := 5439691, preBonus := 5834170, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338222, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338243, updateProofs := some (231551, 377046), numericProof := 75886, slack := 0}
noncomputable def case824 : PhysicalCase := ⟨1,317,.north,.push 291 (.stay 265),frame824⟩
theorem frame824_checked : CountedLocalCaseData.check data frame824 = true := by decide +kernel
theorem case824_fitted : fits case824 = true := by decide +kernel
noncomputable def frame825 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 19, changes := [(317, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832816, afterBeta := 5439691, afterBonus := 5832817, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338264, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (233281, 377067), numericProof := 75887, slack := 7}
noncomputable def case825 : PhysicalCase := ⟨1,265,.south,.push 291 (.stay 317),frame825⟩
theorem frame825_checked : CountedLocalCaseData.check data frame825 = true := by decide +kernel
theorem case825_fitted : fits case825 = true := by decide +kernel
noncomputable def frame826 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 19, changes := [(292, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832817, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338285, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (234997, 377088), numericProof := 75888, slack := 2}
noncomputable def case826 : PhysicalCase := ⟨1,290,.east,.push 291 (.stay 292),frame826⟩
theorem frame826_checked : CountedLocalCaseData.check data frame826 = true := by decide +kernel
theorem case826_fitted : fits case826 = true := by decide +kernel
noncomputable def frame827 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 19, changes := [(290, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832819, afterBeta := 5439691, afterBonus := 5832817, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338287, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (236711, 377109), numericProof := 75889, slack := 2}
noncomputable def case827 : PhysicalCase := ⟨1,292,.west,.push 291 (.stay 290),frame827⟩
theorem frame827_checked : CountedLocalCaseData.check data frame827 = true := by decide +kernel
theorem case827_fitted : fits case827 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
