import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame828 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 20, changes := [(294, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832711, afterBeta := 5439691, afterBonus := 5832710, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1219210, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (252384, 252307), numericProof := 74454, slack := 5}
noncomputable def case828 : PhysicalCase := ⟨0,292,.east,.push 293 (.stay 294),frame828⟩
theorem frame828_checked : CountedLocalCaseData.check data frame828 = true := by decide +kernel
theorem case828_fitted : fits case828 = true := by decide +kernel
noncomputable def frame829 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 20, changes := [(292, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832709, afterBeta := 5439691, afterBonus := 5832710, preBeta := 5439691, preBonus := 5833594, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1223841, restrictionAfterBeta := 8531, restrictionAfterBonus := 1228216, updateProofs := some (257919, 257842), numericProof := 74455, slack := 0}
noncomputable def case829 : PhysicalCase := ⟨0,294,.west,.push 293 (.stay 292),frame829⟩
theorem frame829_checked : CountedLocalCaseData.check data frame829 = true := by decide +kernel
theorem case829_fitted : fits case829 = true := by decide +kernel
noncomputable def frame830 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 20, changes := [(270, true), (296, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1232933, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (262583, 262506), numericProof := 74456, slack := 1}
noncomputable def case830 : PhysicalCase := ⟨0,322,.north,.push 296 (.stay 270),frame830⟩
theorem frame830_checked : CountedLocalCaseData.check data frame830 = true := by decide +kernel
theorem case830_fitted : fits case830 = true := by decide +kernel
noncomputable def frame831 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 20, changes := [(322, true), (296, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1232933, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (267420, 267343), numericProof := 74456, slack := 1}
noncomputable def case831 : PhysicalCase := ⟨0,270,.south,.push 296 (.stay 322),frame831⟩
theorem frame831_checked : CountedLocalCaseData.check data frame831 = true := by decide +kernel
theorem case831_fitted : fits case831 = true := by decide +kernel
noncomputable def frame832 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 20, changes := [(319, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832743, afterBeta := 5439691, afterBonus := 5832751, preBeta := 5439691, preBonus := 5833596, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1234587, restrictionAfterBeta := 8531, restrictionAfterBonus := 1236239, updateProofs := some (269156, 269079), numericProof := 74457, slack := 0}
noncomputable def case832 : PhysicalCase := ⟨0,317,.east,.push 318 (.stay 319),frame832⟩
theorem frame832_checked : CountedLocalCaseData.check data frame832 = true := by decide +kernel
theorem case832_fitted : fits case832 = true := by decide +kernel
noncomputable def frame833 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 20, changes := [(317, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832708, afterBeta := 5439691, afterBonus := 5832751, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1241725, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (270886, 270809), numericProof := 74458, slack := 3}
noncomputable def case833 : PhysicalCase := ⟨0,319,.west,.push 318 (.stay 317),frame833⟩
theorem frame833_checked : CountedLocalCaseData.check data frame833 = true := by decide +kernel
theorem case833_fitted : fits case833 = true := by decide +kernel
noncomputable def frame834 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 20, changes := [(293, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832706, afterBeta := 5439691, afterBonus := 5832708, preBeta := 5439691, preBonus := 5833599, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1247248, restrictionAfterBeta := 8531, restrictionAfterBonus := 1251653, updateProofs := some (276451, 276374), numericProof := 74459, slack := 0}
noncomputable def case834 : PhysicalCase := ⟨0,345,.north,.push 319 (.stay 293),frame834⟩
theorem frame834_checked : CountedLocalCaseData.check data frame834 = true := by decide +kernel
theorem case834_fitted : fits case834 = true := by decide +kernel
noncomputable def frame835 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 20, changes := [(345, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832710, afterBeta := 5439691, afterBonus := 5832708, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1257109, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (282031, 281954), numericProof := 74460, slack := 2}
noncomputable def case835 : PhysicalCase := ⟨0,293,.south,.push 319 (.stay 345),frame835⟩
theorem frame835_checked : CountedLocalCaseData.check data frame835 = true := by decide +kernel
theorem case835_fitted : fits case835 = true := by decide +kernel
noncomputable def frame836 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 20, changes := [(320, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832751, afterBeta := 5439691, afterBonus := 5832708, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1258765, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (287603, 287526), numericProof := 74461, slack := 4}
noncomputable def case836 : PhysicalCase := ⟨0,318,.east,.push 319 (.stay 320),frame836⟩
theorem frame836_checked : CountedLocalCaseData.check data frame836 = true := by decide +kernel
theorem case836_fitted : fits case836 = true := by decide +kernel
noncomputable def frame837 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 20, changes := [(318, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832709, afterBeta := 5439691, afterBonus := 5832708, preBeta := 5439691, preBonus := 5833603, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1264263, restrictionAfterBeta := 8531, restrictionAfterBonus := 1269745, updateProofs := some (293175, 293098), numericProof := 74462, slack := 2}
noncomputable def case837 : PhysicalCase := ⟨0,320,.west,.push 319 (.stay 318),frame837⟩
theorem frame837_checked : CountedLocalCaseData.check data frame837 = true := by decide +kernel
theorem case837_fitted : fits case837 = true := by decide +kernel
noncomputable def frame838 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 20, changes := [(296, true), (322, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1274504, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (297970, 297893), numericProof := 74463, slack := 1}
noncomputable def case838 : PhysicalCase := ⟨0,348,.north,.push 322 (.stay 296),frame838⟩
theorem frame838_checked : CountedLocalCaseData.check data frame838 = true := by decide +kernel
theorem case838_fitted : fits case838 = true := by decide +kernel
noncomputable def frame839 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 20, changes := [(348, true), (322, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1274504, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (302816, 302739), numericProof := 74463, slack := 1}
noncomputable def case839 : PhysicalCase := ⟨0,296,.south,.push 322 (.stay 348),frame839⟩
theorem frame839_checked : CountedLocalCaseData.check data frame839 = true := by decide +kernel
theorem case839_fitted : fits case839 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
