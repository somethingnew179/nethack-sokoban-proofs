import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame816 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 20, changes := [(272, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439701, afterBonus := 5832713, preBeta := 5439687, preBonus := 5833579, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1184549, restrictionAfterBeta := 829, restrictionAfterBonus := 1186438, updateProofs := some (221039, 220949), numericProof := 73066, slack := 1}
noncomputable def case816 : PhysicalCase := ⟨0,270,.east,.push 271 (.stay 272),frame816⟩
theorem frame816_checked : CountedLocalCaseData.check data frame816 = true := by decide +kernel
theorem case816_fitted : fits case816 = true := by decide +kernel
noncomputable def frame817 : CountedLocalCase.Frame := {bindings := [(270, false), (271, true), (272, false)], budget := 20, changes := [(270, true), (271, false)], beforeBeta := 5439691, beforeBonus := 5832716, afterBeta := 5439701, afterBonus := 5832713, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 1169168, restrictionBeforeBonus := 1188152, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (223611, 223521), numericProof := 73067, slack := 1}
noncomputable def case817 : PhysicalCase := ⟨0,272,.west,.push 271 (.stay 270),frame817⟩
theorem frame817_checked : CountedLocalCaseData.check data frame817 = true := by decide +kernel
theorem case817_fitted : fits case817 = true := by decide +kernel
noncomputable def frame818 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 20, changes := [(290, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1189628, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (225168, 225091), numericProof := 73068, slack := 0}
noncomputable def case818 : PhysicalCase := ⟨0,288,.east,.push 289 (.stay 290),frame818⟩
theorem frame818_checked : CountedLocalCaseData.check data frame818 = true := by decide +kernel
theorem case818_fitted : fits case818 = true := by decide +kernel
noncomputable def frame819 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 20, changes := [(288, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1189628, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (226719, 226642), numericProof := 73069, slack := 5}
noncomputable def case819 : PhysicalCase := ⟨0,290,.west,.push 289 (.stay 288),frame819⟩
theorem frame819_checked : CountedLocalCaseData.check data frame819 = true := by decide +kernel
theorem case819_fitted : fits case819 = true := by decide +kernel
noncomputable def frame820 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 20, changes := [(291, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 5833582, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1191107, restrictionAfterBeta := 8531, restrictionAfterBonus := 1191807, updateProofs := some (228281, 228204), numericProof := 73070, slack := 0}
noncomputable def case820 : PhysicalCase := ⟨0,289,.east,.push 290 (.stay 291),frame820⟩
theorem frame820_checked : CountedLocalCaseData.check data frame820 = true := by decide +kernel
theorem case820_fitted : fits case820 = true := by decide +kernel
noncomputable def frame821 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 20, changes := [(289, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832743, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1192690, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (229835, 229758), numericProof := 73071, slack := 2}
noncomputable def case821 : PhysicalCase := ⟨0,291,.west,.push 290 (.stay 289),frame821⟩
theorem frame821_checked : CountedLocalCaseData.check data frame821 = true := by decide +kernel
theorem case821_fitted : fits case821 = true := by decide +kernel
noncomputable def frame822 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 20, changes := [(265, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832743, afterBeta := 5439691, afterBonus := 5832743, preBeta := 5439691, preBonus := 5833585, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1194325, restrictionAfterBeta := 8531, restrictionAfterBonus := 1195702, updateProofs := some (231551, 231474), numericProof := 73072, slack := 0}
noncomputable def case822 : PhysicalCase := ⟨0,317,.north,.push 291 (.stay 265),frame822⟩
theorem frame822_checked : CountedLocalCaseData.check data frame822 = true := by decide +kernel
theorem case822_fitted : fits case822 = true := by decide +kernel
noncomputable def frame823 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 20, changes := [(317, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832746, afterBeta := 5439691, afterBonus := 5832743, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1197474, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (233281, 233204), numericProof := 73073, slack := 7}
noncomputable def case823 : PhysicalCase := ⟨0,265,.south,.push 291 (.stay 317),frame823⟩
theorem frame823_checked : CountedLocalCaseData.check data frame823 = true := by decide +kernel
theorem case823_fitted : fits case823 = true := by decide +kernel
noncomputable def frame824 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 20, changes := [(292, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832743, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1198960, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (234997, 234920), numericProof := 73074, slack := 2}
noncomputable def case824 : PhysicalCase := ⟨0,290,.east,.push 291 (.stay 292),frame824⟩
theorem frame824_checked : CountedLocalCaseData.check data frame824 = true := by decide +kernel
theorem case824_fitted : fits case824 = true := by decide +kernel
noncomputable def frame825 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 20, changes := [(290, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832711, afterBeta := 5439691, afterBonus := 5832743, preBeta := 5439691, preBonus := 5833589, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1203254, restrictionAfterBeta := 8531, restrictionAfterBonus := 1204055, updateProofs := some (236711, 236634), numericProof := 74451, slack := 2}
noncomputable def case825 : PhysicalCase := ⟨0,292,.west,.push 291 (.stay 290),frame825⟩
theorem frame825_checked : CountedLocalCaseData.check data frame825 = true := by decide +kernel
theorem case825_fitted : fits case825 = true := by decide +kernel
noncomputable def frame826 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 20, changes := [(293, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832743, afterBeta := 5439691, afterBonus := 5832711, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1205693, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (241780, 241703), numericProof := 74452, slack := 2}
noncomputable def case826 : PhysicalCase := ⟨0,291,.east,.push 292 (.stay 293),frame826⟩
theorem frame826_checked : CountedLocalCaseData.check data frame826 = true := by decide +kernel
theorem case826_fitted : fits case826 = true := by decide +kernel
noncomputable def frame827 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 20, changes := [(291, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832710, afterBeta := 5439691, afterBonus := 5832711, preBeta := 5439691, preBonus := 5833592, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1210317, restrictionAfterBeta := 8531, restrictionAfterBonus := 1214219, updateProofs := some (246843, 246766), numericProof := 74453, slack := 0}
noncomputable def case827 : PhysicalCase := ⟨0,293,.west,.push 292 (.stay 291),frame827⟩
theorem frame827_checked : CountedLocalCaseData.check data frame827 = true := by decide +kernel
theorem case827_fitted : fits case827 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
