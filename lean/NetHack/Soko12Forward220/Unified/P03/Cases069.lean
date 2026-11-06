import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame828 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 17, changes := [(265, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 5834820, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343195, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343199, updateProofs := some (231551, 378516), numericProof := 77249, slack := 0}
noncomputable def case828 : PhysicalCase := ⟨3,317,.north,.push 291 (.stay 265),frame828⟩
theorem frame828_checked : CountedLocalCaseData.check data frame828 = true := by decide +kernel
theorem case828_fitted : fits case828 = true := by decide +kernel
noncomputable def frame829 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 17, changes := [(317, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832879, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343203, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (233281, 378520), numericProof := 77250, slack := 7}
noncomputable def case829 : PhysicalCase := ⟨3,265,.south,.push 291 (.stay 317),frame829⟩
theorem frame829_checked : CountedLocalCaseData.check data frame829 = true := by decide +kernel
theorem case829_fitted : fits case829 = true := by decide +kernel
noncomputable def frame830 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 17, changes := [(292, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343207, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (234997, 378524), numericProof := 77251, slack := 2}
noncomputable def case830 : PhysicalCase := ⟨3,290,.east,.push 291 (.stay 292),frame830⟩
theorem frame830_checked : CountedLocalCaseData.check data frame830 = true := by decide +kernel
theorem case830_fitted : fits case830 = true := by decide +kernel
noncomputable def frame831 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 17, changes := [(290, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343207, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (236711, 378528), numericProof := 77251, slack := 2}
noncomputable def case831 : PhysicalCase := ⟨3,292,.west,.push 291 (.stay 290),frame831⟩
theorem frame831_checked : CountedLocalCaseData.check data frame831 = true := by decide +kernel
theorem case831_fitted : fits case831 = true := by decide +kernel
noncomputable def frame832 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 17, changes := [(293, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343211, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (241780, 378532), numericProof := 77252, slack := 2}
noncomputable def case832 : PhysicalCase := ⟨3,291,.east,.push 292 (.stay 293),frame832⟩
theorem frame832_checked : CountedLocalCaseData.check data frame832 = true := by decide +kernel
theorem case832_fitted : fits case832 = true := by decide +kernel
noncomputable def frame833 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 17, changes := [(291, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343211, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (246843, 378536), numericProof := 77253, slack := 0}
noncomputable def case833 : PhysicalCase := ⟨3,293,.west,.push 292 (.stay 291),frame833⟩
theorem frame833_checked : CountedLocalCaseData.check data frame833 = true := by decide +kernel
theorem case833_fitted : fits case833 = true := by decide +kernel
noncomputable def frame834 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 17, changes := [(294, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343215, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (252384, 378540), numericProof := 77254, slack := 5}
noncomputable def case834 : PhysicalCase := ⟨3,292,.east,.push 293 (.stay 294),frame834⟩
theorem frame834_checked : CountedLocalCaseData.check data frame834 = true := by decide +kernel
theorem case834_fitted : fits case834 = true := by decide +kernel
noncomputable def frame835 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 17, changes := [(292, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343215, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (257919, 378544), numericProof := 77255, slack := 0}
noncomputable def case835 : PhysicalCase := ⟨3,294,.west,.push 293 (.stay 292),frame835⟩
theorem frame835_checked : CountedLocalCaseData.check data frame835 = true := by decide +kernel
theorem case835_fitted : fits case835 = true := by decide +kernel
noncomputable def frame836 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 17, changes := [(270, true), (296, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (262583, 257920), numericProof := 77256, slack := 1}
noncomputable def case836 : PhysicalCase := ⟨3,322,.north,.push 296 (.stay 270),frame836⟩
theorem frame836_checked : CountedLocalCaseData.check data frame836 = true := by decide +kernel
theorem case836_fitted : fits case836 = true := by decide +kernel
noncomputable def frame837 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 17, changes := [(322, true), (296, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (267420, 262584), numericProof := 77256, slack := 1}
noncomputable def case837 : PhysicalCase := ⟨3,270,.south,.push 296 (.stay 322),frame837⟩
theorem frame837_checked : CountedLocalCaseData.check data frame837 = true := by decide +kernel
theorem case837_fitted : fits case837 = true := by decide +kernel
noncomputable def frame838 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 17, changes := [(319, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832881, preBeta := 5439691, preBonus := 5834822, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343219, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343223, updateProofs := some (269156, 378548), numericProof := 77257, slack := 0}
noncomputable def case838 : PhysicalCase := ⟨3,317,.east,.push 318 (.stay 319),frame838⟩
theorem frame838_checked : CountedLocalCaseData.check data frame838 = true := by decide +kernel
theorem case838_fitted : fits case838 = true := by decide +kernel
noncomputable def frame839 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 17, changes := [(317, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832881, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343227, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (270886, 378552), numericProof := 77258, slack := 3}
noncomputable def case839 : PhysicalCase := ⟨3,319,.west,.push 318 (.stay 317),frame839⟩
theorem frame839_checked : CountedLocalCaseData.check data frame839 = true := by decide +kernel
theorem case839_fitted : fits case839 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
