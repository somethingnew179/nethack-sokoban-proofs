import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame828 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 19, changes := [(293, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832817, afterBeta := 5439691, afterBonus := 5832819, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338308, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (241780, 377130), numericProof := 75890, slack := 2}
noncomputable def case828 : PhysicalCase := ⟨1,291,.east,.push 292 (.stay 293),frame828⟩
theorem frame828_checked : CountedLocalCaseData.check data frame828 = true := by decide +kernel
theorem case828_fitted : fits case828 = true := by decide +kernel
noncomputable def frame829 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 19, changes := [(291, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832821, afterBeta := 5439691, afterBonus := 5832819, preBeta := 5439691, preBonus := 5834175, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338310, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338312, updateProofs := some (246843, 377151), numericProof := 75891, slack := 0}
noncomputable def case829 : PhysicalCase := ⟨1,293,.west,.push 292 (.stay 291),frame829⟩
theorem frame829_checked : CountedLocalCaseData.check data frame829 = true := by decide +kernel
theorem case829_fitted : fits case829 = true := by decide +kernel
noncomputable def frame830 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 19, changes := [(294, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832819, afterBeta := 5439691, afterBonus := 5832821, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338333, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (252384, 377172), numericProof := 75892, slack := 5}
noncomputable def case830 : PhysicalCase := ⟨1,292,.east,.push 293 (.stay 294),frame830⟩
theorem frame830_checked : CountedLocalCaseData.check data frame830 = true := by decide +kernel
theorem case830_fitted : fits case830 = true := by decide +kernel
noncomputable def frame831 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 19, changes := [(292, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832825, afterBeta := 5439691, afterBonus := 5832821, preBeta := 5439691, preBonus := 5834177, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338335, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338337, updateProofs := some (257919, 377193), numericProof := 75893, slack := 0}
noncomputable def case831 : PhysicalCase := ⟨1,294,.west,.push 293 (.stay 292),frame831⟩
theorem frame831_checked : CountedLocalCaseData.check data frame831 = true := by decide +kernel
theorem case831_fitted : fits case831 = true := by decide +kernel
noncomputable def frame832 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 19, changes := [(270, true), (296, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338339, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (262583, 377195), numericProof := 75894, slack := 1}
noncomputable def case832 : PhysicalCase := ⟨1,322,.north,.push 296 (.stay 270),frame832⟩
theorem frame832_checked : CountedLocalCaseData.check data frame832 = true := by decide +kernel
theorem case832_fitted : fits case832 = true := by decide +kernel
noncomputable def frame833 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 19, changes := [(322, true), (296, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338339, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (267420, 377197), numericProof := 75894, slack := 1}
noncomputable def case833 : PhysicalCase := ⟨1,270,.south,.push 296 (.stay 322),frame833⟩
theorem frame833_checked : CountedLocalCaseData.check data frame833 = true := by decide +kernel
theorem case833_fitted : fits case833 = true := by decide +kernel
noncomputable def frame834 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 19, changes := [(319, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832817, afterBeta := 5439691, afterBonus := 5832820, preBeta := 5439691, preBonus := 5834179, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338360, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338381, updateProofs := some (269156, 377218), numericProof := 75895, slack := 0}
noncomputable def case834 : PhysicalCase := ⟨1,317,.east,.push 318 (.stay 319),frame834⟩
theorem frame834_checked : CountedLocalCaseData.check data frame834 = true := by decide +kernel
theorem case834_fitted : fits case834 = true := by decide +kernel
noncomputable def frame835 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 19, changes := [(317, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832822, afterBeta := 5439691, afterBonus := 5832820, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338402, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (270886, 377239), numericProof := 75896, slack := 3}
noncomputable def case835 : PhysicalCase := ⟨1,319,.west,.push 318 (.stay 317),frame835⟩
theorem frame835_checked : CountedLocalCaseData.check data frame835 = true := by decide +kernel
theorem case835_fitted : fits case835 = true := by decide +kernel
noncomputable def frame836 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 19, changes := [(293, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832824, afterBeta := 5439691, afterBonus := 5832822, preBeta := 5439691, preBonus := 5834182, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338423, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338425, updateProofs := some (276451, 377260), numericProof := 75897, slack := 0}
noncomputable def case836 : PhysicalCase := ⟨1,345,.north,.push 319 (.stay 293),frame836⟩
theorem frame836_checked : CountedLocalCaseData.check data frame836 = true := by decide +kernel
theorem case836_fitted : fits case836 = true := by decide +kernel
noncomputable def frame837 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 19, changes := [(345, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832821, afterBeta := 5439691, afterBonus := 5832822, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338446, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (282031, 377281), numericProof := 75898, slack := 2}
noncomputable def case837 : PhysicalCase := ⟨1,293,.south,.push 319 (.stay 345),frame837⟩
theorem frame837_checked : CountedLocalCaseData.check data frame837 = true := by decide +kernel
theorem case837_fitted : fits case837 = true := by decide +kernel
noncomputable def frame838 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 19, changes := [(320, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832820, afterBeta := 5439691, afterBonus := 5832822, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338467, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (287603, 377302), numericProof := 75899, slack := 4}
noncomputable def case838 : PhysicalCase := ⟨1,318,.east,.push 319 (.stay 320),frame838⟩
theorem frame838_checked : CountedLocalCaseData.check data frame838 = true := by decide +kernel
theorem case838_fitted : fits case838 = true := by decide +kernel
noncomputable def frame839 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 19, changes := [(318, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832825, afterBeta := 5439691, afterBonus := 5832822, preBeta := 5439691, preBonus := 5834186, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338488, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338509, updateProofs := some (293175, 377323), numericProof := 75900, slack := 2}
noncomputable def case839 : PhysicalCase := ⟨1,320,.west,.push 319 (.stay 318),frame839⟩
theorem frame839_checked : CountedLocalCaseData.check data frame839 = true := by decide +kernel
theorem case839_fitted : fits case839 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
