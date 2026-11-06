import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame840 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 19, changes := [(296, true), (322, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338511, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (297970, 377325), numericProof := 75901, slack := 1}
noncomputable def case840 : PhysicalCase := ⟨1,348,.north,.push 322 (.stay 296),frame840⟩
theorem frame840_checked : CountedLocalCaseData.check data frame840 = true := by decide +kernel
theorem case840_fitted : fits case840 = true := by decide +kernel
noncomputable def frame841 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 19, changes := [(348, true), (322, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338511, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (302816, 377327), numericProof := 75901, slack := 1}
noncomputable def case841 : PhysicalCase := ⟨1,296,.south,.push 322 (.stay 348),frame841⟩
theorem frame841_checked : CountedLocalCaseData.check data frame841 = true := by decide +kernel
theorem case841_fitted : fits case841 = true := by decide +kernel
noncomputable def frame842 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 19, changes := [(319, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832823, afterBeta := 5439691, afterBonus := 5832824, preBeta := 5439691, preBonus := 5834188, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338532, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338534, updateProofs := some (308429, 377348), numericProof := 75902, slack := 0}
noncomputable def case842 : PhysicalCase := ⟨1,371,.north,.push 345 (.stay 319),frame842⟩
theorem frame842_checked : CountedLocalCaseData.check data frame842 = true := by decide +kernel
theorem case842_fitted : fits case842 = true := by decide +kernel
noncomputable def frame843 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 19, changes := [(371, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832822, afterBeta := 5439691, afterBonus := 5832824, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338536, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (314054, 377369), numericProof := 75903, slack := 2}
noncomputable def case843 : PhysicalCase := ⟨1,319,.south,.push 345 (.stay 371),frame843⟩
theorem frame843_checked : CountedLocalCaseData.check data frame843 = true := by decide +kernel
theorem case843_fitted : fits case843 = true := by decide +kernel
noncomputable def frame844 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 19, changes := [(322, true), (348, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338538, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (318891, 377371), numericProof := 75904, slack := 1}
noncomputable def case844 : PhysicalCase := ⟨1,374,.north,.push 348 (.stay 322),frame844⟩
theorem frame844_checked : CountedLocalCaseData.check data frame844 = true := by decide +kernel
theorem case844_fitted : fits case844 = true := by decide +kernel
noncomputable def frame845 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 19, changes := [(374, true), (348, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338538, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (323752, 377373), numericProof := 75904, slack := 1}
noncomputable def case845 : PhysicalCase := ⟨1,322,.south,.push 348 (.stay 374),frame845⟩
theorem frame845_checked : CountedLocalCaseData.check data frame845 = true := by decide +kernel
theorem case845_fitted : fits case845 = true := by decide +kernel
noncomputable def frame846 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 19, changes := [(345, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832823, afterBeta := 5439691, afterBonus := 5832823, preBeta := 5439691, preBonus := 5834190, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338559, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338561, updateProofs := some (329389, 377394), numericProof := 75905, slack := 0}
noncomputable def case846 : PhysicalCase := ⟨1,397,.north,.push 371 (.stay 345),frame846⟩
theorem frame846_checked : CountedLocalCaseData.check data frame846 = true := by decide +kernel
theorem case846_fitted : fits case846 = true := by decide +kernel
noncomputable def frame847 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 19, changes := [(397, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832824, afterBeta := 5439691, afterBonus := 5832823, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338563, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (335039, 377415), numericProof := 75906, slack := 2}
noncomputable def case847 : PhysicalCase := ⟨1,345,.south,.push 371 (.stay 397),frame847⟩
theorem frame847_checked : CountedLocalCaseData.check data frame847 = true := by decide +kernel
theorem case847_fitted : fits case847 = true := by decide +kernel
noncomputable def frame848 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 19, changes := [(372, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832823, afterBeta := 5439691, afterBonus := 5832823, preBeta := 5439691, preBonus := 5834192, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338584, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338605, updateProofs := some (340681, 377436), numericProof := 75907, slack := 2}
noncomputable def case848 : PhysicalCase := ⟨1,370,.east,.push 371 (.stay 372),frame848⟩
theorem frame848_checked : CountedLocalCaseData.check data frame848 = true := by decide +kernel
theorem case848_fitted : fits case848 = true := by decide +kernel
noncomputable def frame849 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 19, changes := [(370, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832823, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338607, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (346314, 377457), numericProof := 75908, slack := 2}
noncomputable def case849 : PhysicalCase := ⟨1,372,.west,.push 371 (.stay 370),frame849⟩
theorem frame849_checked : CountedLocalCaseData.check data frame849 = true := by decide +kernel
theorem case849_fitted : fits case849 = true := by decide +kernel
noncomputable def frame850 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 19, changes := [(373, true), (372, false)], beforeBeta := 5439691, beforeBonus := 5832823, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338628, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (351172, 377459), numericProof := 75909, slack := 1}
noncomputable def case850 : PhysicalCase := ⟨1,371,.east,.push 372 (.stay 373),frame850⟩
theorem frame850_checked : CountedLocalCaseData.check data frame850 = true := by decide +kernel
theorem case850_fitted : fits case850 = true := by decide +kernel
noncomputable def frame851 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 19, changes := [(371, true), (372, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338630, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (356024, 377461), numericProof := 75910, slack := 0}
noncomputable def case851 : PhysicalCase := ⟨1,373,.west,.push 372 (.stay 371),frame851⟩
theorem frame851_checked : CountedLocalCaseData.check data frame851 = true := by decide +kernel
theorem case851_fitted : fits case851 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
