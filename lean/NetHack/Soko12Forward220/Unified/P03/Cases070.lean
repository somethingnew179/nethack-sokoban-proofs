import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame840 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 17, changes := [(293, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343231, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (276451, 378556), numericProof := 77259, slack := 0}
noncomputable def case840 : PhysicalCase := ⟨3,345,.north,.push 319 (.stay 293),frame840⟩
theorem frame840_checked : CountedLocalCaseData.check data frame840 = true := by decide +kernel
theorem case840_fitted : fits case840 = true := by decide +kernel
noncomputable def frame841 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 17, changes := [(345, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343235, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (282031, 378560), numericProof := 77260, slack := 2}
noncomputable def case841 : PhysicalCase := ⟨3,293,.south,.push 319 (.stay 345),frame841⟩
theorem frame841_checked : CountedLocalCaseData.check data frame841 = true := by decide +kernel
theorem case841_fitted : fits case841 = true := by decide +kernel
noncomputable def frame842 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 17, changes := [(320, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832881, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343239, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (287603, 378564), numericProof := 77261, slack := 4}
noncomputable def case842 : PhysicalCase := ⟨3,318,.east,.push 319 (.stay 320),frame842⟩
theorem frame842_checked : CountedLocalCaseData.check data frame842 = true := by decide +kernel
theorem case842_fitted : fits case842 = true := by decide +kernel
noncomputable def frame843 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 17, changes := [(318, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 5834822, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343243, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343247, updateProofs := some (293175, 378568), numericProof := 77262, slack := 2}
noncomputable def case843 : PhysicalCase := ⟨3,320,.west,.push 319 (.stay 318),frame843⟩
theorem frame843_checked : CountedLocalCaseData.check data frame843 = true := by decide +kernel
theorem case843_fitted : fits case843 = true := by decide +kernel
noncomputable def frame844 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 17, changes := [(296, true), (322, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (297970, 293176), numericProof := 77263, slack := 1}
noncomputable def case844 : PhysicalCase := ⟨3,348,.north,.push 322 (.stay 296),frame844⟩
theorem frame844_checked : CountedLocalCaseData.check data frame844 = true := by decide +kernel
theorem case844_fitted : fits case844 = true := by decide +kernel
noncomputable def frame845 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 17, changes := [(348, true), (322, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (302816, 297971), numericProof := 77263, slack := 1}
noncomputable def case845 : PhysicalCase := ⟨3,296,.south,.push 322 (.stay 348),frame845⟩
theorem frame845_checked : CountedLocalCaseData.check data frame845 = true := by decide +kernel
theorem case845_fitted : fits case845 = true := by decide +kernel
noncomputable def frame846 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 17, changes := [(319, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343251, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (308429, 378572), numericProof := 77264, slack := 0}
noncomputable def case846 : PhysicalCase := ⟨3,371,.north,.push 345 (.stay 319),frame846⟩
theorem frame846_checked : CountedLocalCaseData.check data frame846 = true := by decide +kernel
theorem case846_fitted : fits case846 = true := by decide +kernel
noncomputable def frame847 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 17, changes := [(371, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343251, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (314054, 378576), numericProof := 77265, slack := 2}
noncomputable def case847 : PhysicalCase := ⟨3,319,.south,.push 345 (.stay 371),frame847⟩
theorem frame847_checked : CountedLocalCaseData.check data frame847 = true := by decide +kernel
theorem case847_fitted : fits case847 = true := by decide +kernel
noncomputable def frame848 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 17, changes := [(322, true), (348, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (318891, 314055), numericProof := 77266, slack := 1}
noncomputable def case848 : PhysicalCase := ⟨3,374,.north,.push 348 (.stay 322),frame848⟩
theorem frame848_checked : CountedLocalCaseData.check data frame848 = true := by decide +kernel
theorem case848_fitted : fits case848 = true := by decide +kernel
noncomputable def frame849 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 17, changes := [(374, true), (348, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (323752, 318892), numericProof := 77266, slack := 1}
noncomputable def case849 : PhysicalCase := ⟨3,322,.south,.push 348 (.stay 374),frame849⟩
theorem frame849_checked : CountedLocalCaseData.check data frame849 = true := by decide +kernel
theorem case849_fitted : fits case849 = true := by decide +kernel
noncomputable def frame850 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 17, changes := [(345, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343255, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (329389, 378580), numericProof := 77267, slack := 0}
noncomputable def case850 : PhysicalCase := ⟨3,397,.north,.push 371 (.stay 345),frame850⟩
theorem frame850_checked : CountedLocalCaseData.check data frame850 = true := by decide +kernel
theorem case850_fitted : fits case850 = true := by decide +kernel
noncomputable def frame851 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 17, changes := [(397, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343255, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (335039, 378584), numericProof := 77268, slack := 2}
noncomputable def case851 : PhysicalCase := ⟨3,345,.south,.push 371 (.stay 397),frame851⟩
theorem frame851_checked : CountedLocalCaseData.check data frame851 = true := by decide +kernel
theorem case851_fitted : fits case851 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
