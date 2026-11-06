import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame792 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 20, changes := [(218, true), (244, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832714, preBeta := 5439691, preBonus := 5833525, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1103046, restrictionAfterBeta := 8531, restrictionAfterBonus := 1105814, updateProofs := some (157267, 157193), numericProof := 58366, slack := 0}
noncomputable def case792 : PhysicalCase := ⟨0,270,.north,.push 244 (.stay 218),frame792⟩
theorem frame792_checked : CountedLocalCaseData.check data frame792 = true := by decide +kernel
theorem case792_fitted : fits case792 = true := by decide +kernel
noncomputable def frame793 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 20, changes := [(270, true), (244, false)], beforeBeta := 5439691, beforeBonus := 5832728, afterBeta := 5439691, afterBonus := 5832714, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1108176, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (161757, 161683), numericProof := 58367, slack := 2}
noncomputable def case793 : PhysicalCase := ⟨0,218,.south,.push 244 (.stay 270),frame793⟩
theorem frame793_checked : CountedLocalCaseData.check data frame793 = true := by decide +kernel
theorem case793_fitted : fits case793 = true := by decide +kernel
noncomputable def frame794 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 20, changes := [(219, true), (245, false)], beforeBeta := 5439701, beforeBonus := 5832713, afterBeta := 5439691, afterBonus := 5832715, preBeta := 5439691, preBonus := 5833529, restrictionBeforeBeta := 426739, restrictionBeforeBonus := 1110544, restrictionAfterBeta := 422199, restrictionAfterBonus := 1112620, updateProofs := some (166105, 166031), numericProof := 58842, slack := 0}
noncomputable def case794 : PhysicalCase := ⟨0,271,.north,.push 245 (.stay 219),frame794⟩
theorem frame794_checked : CountedLocalCaseData.check data frame794 = true := by decide +kernel
theorem case794_fitted : fits case794 = true := by decide +kernel
noncomputable def frame795 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 20, changes := [(271, true), (245, false)], beforeBeta := 5439691, beforeBonus := 5832717, afterBeta := 5439691, afterBonus := 5832715, preBeta := 5441377, preBonus := 5833532, restrictionBeforeBeta := 422199, restrictionBeforeBonus := 1116376, restrictionAfterBeta := 1116377, restrictionAfterBonus := 1119456, updateProofs := some (170833, 170756), numericProof := 60383, slack := 1}
noncomputable def case795 : PhysicalCase := ⟨0,219,.south,.push 245 (.stay 271),frame795⟩
theorem frame795_checked : CountedLocalCaseData.check data frame795 = true := by decide +kernel
theorem case795_fitted : fits case795 = true := by decide +kernel
noncomputable def frame796 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 20, changes := [(246, true), (245, false)], beforeBeta := 5439691, beforeBonus := 5832714, afterBeta := 5439691, afterBonus := 5832715, preBeta := 5439691, preBonus := 5833535, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1123718, restrictionAfterBeta := 8531, restrictionAfterBonus := 1127238, updateProofs := some (175422, 175348), numericProof := 60738, slack := 1}
noncomputable def case796 : PhysicalCase := ⟨0,244,.east,.push 245 (.stay 246),frame796⟩
theorem frame796_checked : CountedLocalCaseData.check data frame796 = true := by decide +kernel
theorem case796_fitted : fits case796 = true := by decide +kernel
noncomputable def frame797 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 20, changes := [(244, true), (245, false)], beforeBeta := 5439691, beforeBonus := 5832741, afterBeta := 5439691, afterBonus := 5832715, preBeta := 5439691, preBonus := 5833538, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1128665, restrictionAfterBeta := 8531, restrictionAfterBonus := 1129505, updateProofs := some (179950, 179876), numericProof := 60739, slack := 0}
noncomputable def case797 : PhysicalCase := ⟨0,246,.west,.push 245 (.stay 244),frame797⟩
theorem frame797_checked : CountedLocalCaseData.check data frame797 = true := by decide +kernel
theorem case797_fitted : fits case797 = true := by decide +kernel
noncomputable def frame798 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 20, changes := [(220, true), (246, false)], beforeBeta := 5439691, beforeBonus := 5832716, afterBeta := 5439691, afterBonus := 5832741, preBeta := 5439691, preBonus := 5833540, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1131546, restrictionAfterBeta := 8531, restrictionAfterBonus := 1132181, updateProofs := some (181679, 181605), numericProof := 61778, slack := 1}
noncomputable def case798 : PhysicalCase := ⟨0,272,.north,.push 246 (.stay 220),frame798⟩
theorem frame798_checked : CountedLocalCaseData.check data frame798 = true := by decide +kernel
theorem case798_fitted : fits case798 = true := by decide +kernel
noncomputable def frame799 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 20, changes := [(272, true), (246, false)], beforeBeta := 5439691, beforeBonus := 5832718, afterBeta := 5439691, afterBonus := 5832741, preBeta := 5439691, preBonus := 5833543, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1137047, restrictionAfterBeta := 8531, restrictionAfterBonus := 1138336, updateProofs := some (183534, 183457), numericProof := 64561, slack := 1}
noncomputable def case799 : PhysicalCase := ⟨0,220,.south,.push 246 (.stay 272),frame799⟩
theorem frame799_checked : CountedLocalCaseData.check data frame799 = true := by decide +kernel
theorem case799_fitted : fits case799 = true := by decide +kernel
noncomputable def frame800 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 20, changes := [(236, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1139775, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (184959, 184885), numericProof := 64562, slack := 0}
noncomputable def case800 : PhysicalCase := ⟨0,288,.north,.push 262 (.stay 236),frame800⟩
theorem frame800_checked : CountedLocalCaseData.check data frame800 = true := by decide +kernel
theorem case800_fitted : fits case800 = true := by decide +kernel
noncomputable def frame801 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 20, changes := [(288, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1139775, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (186510, 186433), numericProof := 64563, slack := 7}
noncomputable def case801 : PhysicalCase := ⟨0,236,.south,.push 262 (.stay 288),frame801⟩
theorem frame801_checked : CountedLocalCaseData.check data frame801 = true := by decide +kernel
theorem case801_fitted : fits case801 = true := by decide +kernel
noncomputable def frame802 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 20, changes := [(237, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832764, preBeta := 5439691, preBonus := 5833546, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1141206, restrictionAfterBeta := 8531, restrictionAfterBonus := 1142044, updateProofs := some (188005, 187931), numericProof := 64928, slack := 0}
noncomputable def case802 : PhysicalCase := ⟨0,289,.north,.push 263 (.stay 237),frame802⟩
theorem frame802_checked : CountedLocalCaseData.check data frame802 = true := by decide +kernel
theorem case802_fitted : fits case802 = true := by decide +kernel
noncomputable def frame803 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 20, changes := [(289, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832767, afterBeta := 5439691, afterBonus := 5832764, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1142902, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (189522, 189445), numericProof := 64929, slack := 4}
noncomputable def case803 : PhysicalCase := ⟨0,237,.south,.push 263 (.stay 289),frame803⟩
theorem frame803_checked : CountedLocalCaseData.check data frame803 = true := by decide +kernel
theorem case803_fitted : fits case803 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
