import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame828 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 16, changes := [(291, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344493, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (228281, 378839), numericProof := 77781, slack := 0}
noncomputable def case828 : PhysicalCase := ⟨4,289,.east,.push 290 (.stay 291),frame828⟩
theorem frame828_checked : CountedLocalCaseData.check data frame828 = true := by decide +kernel
theorem case828_fitted : fits case828 = true := by decide +kernel
noncomputable def frame829 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 16, changes := [(289, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344493, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (229835, 378842), numericProof := 77782, slack := 2}
noncomputable def case829 : PhysicalCase := ⟨4,291,.west,.push 290 (.stay 289),frame829⟩
theorem frame829_checked : CountedLocalCaseData.check data frame829 = true := by decide +kernel
theorem case829_fitted : fits case829 = true := by decide +kernel
noncomputable def frame830 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 16, changes := [(265, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 5835089, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344496, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344499, updateProofs := some (231551, 378845), numericProof := 77783, slack := 0}
noncomputable def case830 : PhysicalCase := ⟨4,317,.north,.push 291 (.stay 265),frame830⟩
theorem frame830_checked : CountedLocalCaseData.check data frame830 = true := by decide +kernel
theorem case830_fitted : fits case830 = true := by decide +kernel
noncomputable def frame831 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 16, changes := [(317, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832906, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344502, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (233281, 378848), numericProof := 77784, slack := 7}
noncomputable def case831 : PhysicalCase := ⟨4,265,.south,.push 291 (.stay 317),frame831⟩
theorem frame831_checked : CountedLocalCaseData.check data frame831 = true := by decide +kernel
theorem case831_fitted : fits case831 = true := by decide +kernel
noncomputable def frame832 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 16, changes := [(292, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344505, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (234997, 378851), numericProof := 77785, slack := 2}
noncomputable def case832 : PhysicalCase := ⟨4,290,.east,.push 291 (.stay 292),frame832⟩
theorem frame832_checked : CountedLocalCaseData.check data frame832 = true := by decide +kernel
theorem case832_fitted : fits case832 = true := by decide +kernel
noncomputable def frame833 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 16, changes := [(290, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344505, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (236711, 378854), numericProof := 77785, slack := 2}
noncomputable def case833 : PhysicalCase := ⟨4,292,.west,.push 291 (.stay 290),frame833⟩
theorem frame833_checked : CountedLocalCaseData.check data frame833 = true := by decide +kernel
theorem case833_fitted : fits case833 = true := by decide +kernel
noncomputable def frame834 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 16, changes := [(293, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344508, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (241780, 378857), numericProof := 77786, slack := 2}
noncomputable def case834 : PhysicalCase := ⟨4,291,.east,.push 292 (.stay 293),frame834⟩
theorem frame834_checked : CountedLocalCaseData.check data frame834 = true := by decide +kernel
theorem case834_fitted : fits case834 = true := by decide +kernel
noncomputable def frame835 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 16, changes := [(291, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344508, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (246843, 378860), numericProof := 77787, slack := 0}
noncomputable def case835 : PhysicalCase := ⟨4,293,.west,.push 292 (.stay 291),frame835⟩
theorem frame835_checked : CountedLocalCaseData.check data frame835 = true := by decide +kernel
theorem case835_fitted : fits case835 = true := by decide +kernel
noncomputable def frame836 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 16, changes := [(294, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344511, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (252384, 378863), numericProof := 77788, slack := 5}
noncomputable def case836 : PhysicalCase := ⟨4,292,.east,.push 293 (.stay 294),frame836⟩
theorem frame836_checked : CountedLocalCaseData.check data frame836 = true := by decide +kernel
theorem case836_fitted : fits case836 = true := by decide +kernel
noncomputable def frame837 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 16, changes := [(292, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344511, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (257919, 378866), numericProof := 77789, slack := 0}
noncomputable def case837 : PhysicalCase := ⟨4,294,.west,.push 293 (.stay 292),frame837⟩
theorem frame837_checked : CountedLocalCaseData.check data frame837 = true := by decide +kernel
theorem case837_fitted : fits case837 = true := by decide +kernel
noncomputable def frame838 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 16, changes := [(270, true), (296, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (262583, 257920), numericProof := 77790, slack := 1}
noncomputable def case838 : PhysicalCase := ⟨4,322,.north,.push 296 (.stay 270),frame838⟩
theorem frame838_checked : CountedLocalCaseData.check data frame838 = true := by decide +kernel
theorem case838_fitted : fits case838 = true := by decide +kernel
noncomputable def frame839 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 16, changes := [(322, true), (296, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (267420, 262584), numericProof := 77790, slack := 1}
noncomputable def case839 : PhysicalCase := ⟨4,270,.south,.push 296 (.stay 322),frame839⟩
theorem frame839_checked : CountedLocalCaseData.check data frame839 = true := by decide +kernel
theorem case839_fitted : fits case839 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
