import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame816 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 16, changes := [(265, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832902, afterBeta := 5439691, afterBonus := 5832905, preBeta := 5439691, preBonus := 5835083, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344470, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344473, updateProofs := some (198116, 378821), numericProof := 77771, slack := 2}
noncomputable def case816 : PhysicalCase := ⟨4,263,.east,.push 264 (.stay 265),frame816⟩
theorem frame816_checked : CountedLocalCaseData.check data frame816 = true := by decide +kernel
theorem case816_fitted : fits case816 = true := by decide +kernel
noncomputable def frame817 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 16, changes := [(263, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832906, afterBeta := 5439691, afterBonus := 5832905, preBeta := 5439691, preBonus := 5835078, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344476, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344478, updateProofs := some (199972, 378824), numericProof := 77772, slack := 2}
noncomputable def case817 : PhysicalCase := ⟨4,265,.west,.push 264 (.stay 263),frame817⟩
theorem frame817_checked : CountedLocalCaseData.check data frame817 = true := by decide +kernel
theorem case817_fitted : fits case817 = true := by decide +kernel
noncomputable def frame818 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 16, changes := [(239, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832906, preBeta := 5439691, preBonus := 5835086, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344481, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344484, updateProofs := some (201896, 378827), numericProof := 77773, slack := 0}
noncomputable def case818 : PhysicalCase := ⟨4,291,.north,.push 265 (.stay 239),frame818⟩
theorem frame818_checked : CountedLocalCaseData.check data frame818 = true := by decide +kernel
theorem case818_fitted : fits case818 = true := by decide +kernel
noncomputable def frame819 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 16, changes := [(291, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832904, afterBeta := 5439691, afterBonus := 5832906, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344487, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (203881, 378830), numericProof := 77774, slack := 2}
noncomputable def case819 : PhysicalCase := ⟨4,239,.south,.push 265 (.stay 291),frame819⟩
theorem frame819_checked : CountedLocalCaseData.check data frame819 = true := by decide +kernel
theorem case819_fitted : fits case819 = true := by decide +kernel
noncomputable def frame820 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 16, changes := [(244, true), (270, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (208395, 203882), numericProof := 77775, slack := 0}
noncomputable def case820 : PhysicalCase := ⟨4,296,.north,.push 270 (.stay 244),frame820⟩
theorem frame820_checked : CountedLocalCaseData.check data frame820 = true := by decide +kernel
theorem case820_fitted : fits case820 = true := by decide +kernel
noncomputable def frame821 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 16, changes := [(296, true), (270, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (213190, 208396), numericProof := 77776, slack := 1}
noncomputable def case821 : PhysicalCase := ⟨4,244,.south,.push 270 (.stay 296),frame821⟩
theorem frame821_checked : CountedLocalCaseData.check data frame821 = true := by decide +kernel
theorem case821_fitted : fits case821 = true := by decide +kernel
noncomputable def frame822 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 16, changes := [(245, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (215711, 213191), numericProof := 77777, slack := 1}
noncomputable def case822 : PhysicalCase := ⟨4,297,.north,.push 271 (.stay 245),frame822⟩
theorem frame822_checked : CountedLocalCaseData.check data frame822 = true := by decide +kernel
theorem case822_fitted : fits case822 = true := by decide +kernel
noncomputable def frame823 : CountedLocalCase.Frame := {bindings := [(245, false), (271, true), (297, false)], budget := 16, changes := [(297, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (218426, 215712), numericProof := 77777, slack := 1}
noncomputable def case823 : PhysicalCase := ⟨4,245,.south,.push 271 (.stay 297),frame823⟩
theorem frame823_checked : CountedLocalCaseData.check data frame823 = true := by decide +kernel
theorem case823_fitted : fits case823 = true := by decide +kernel
noncomputable def frame824 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 16, changes := [(272, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (221039, 218427), numericProof := 77778, slack := 1}
noncomputable def case824 : PhysicalCase := ⟨4,270,.east,.push 271 (.stay 272),frame824⟩
theorem frame824_checked : CountedLocalCaseData.check data frame824 = true := by decide +kernel
theorem case824_fitted : fits case824 = true := by decide +kernel
noncomputable def frame825 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 16, changes := [(270, true), (271, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439701, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (223611, 221040), numericProof := 77778, slack := 1}
noncomputable def case825 : PhysicalCase := ⟨4,272,.west,.push 271 (.stay 270),frame825⟩
theorem frame825_checked : CountedLocalCaseData.check data frame825 = true := by decide +kernel
theorem case825_fitted : fits case825 = true := by decide +kernel
noncomputable def frame826 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 16, changes := [(290, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344490, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (225168, 378833), numericProof := 77779, slack := 0}
noncomputable def case826 : PhysicalCase := ⟨4,288,.east,.push 289 (.stay 290),frame826⟩
theorem frame826_checked : CountedLocalCaseData.check data frame826 = true := by decide +kernel
theorem case826_fitted : fits case826 = true := by decide +kernel
noncomputable def frame827 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 16, changes := [(288, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344490, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (226719, 378836), numericProof := 77780, slack := 5}
noncomputable def case827 : PhysicalCase := ⟨4,290,.west,.push 289 (.stay 288),frame827⟩
theorem frame827_checked : CountedLocalCaseData.check data frame827 = true := by decide +kernel
theorem case827_fitted : fits case827 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
