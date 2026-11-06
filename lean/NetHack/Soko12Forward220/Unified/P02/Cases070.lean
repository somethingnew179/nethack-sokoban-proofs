import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame840 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 18, changes := [(320, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832851, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341464, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (287603, 378129), numericProof := 76674, slack := 4}
noncomputable def case840 : PhysicalCase := ⟨2,318,.east,.push 319 (.stay 320),frame840⟩
theorem frame840_checked : CountedLocalCaseData.check data frame840 = true := by decide +kernel
theorem case840_fitted : fits case840 = true := by decide +kernel
noncomputable def frame841 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 18, changes := [(318, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 5834507, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341471, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341478, updateProofs := some (293175, 378136), numericProof := 76675, slack := 2}
noncomputable def case841 : PhysicalCase := ⟨2,320,.west,.push 319 (.stay 318),frame841⟩
theorem frame841_checked : CountedLocalCaseData.check data frame841 = true := by decide +kernel
theorem case841_fitted : fits case841 = true := by decide +kernel
noncomputable def frame842 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 18, changes := [(296, true), (322, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (297970, 293176), numericProof := 76676, slack := 1}
noncomputable def case842 : PhysicalCase := ⟨2,348,.north,.push 322 (.stay 296),frame842⟩
theorem frame842_checked : CountedLocalCaseData.check data frame842 = true := by decide +kernel
theorem case842_fitted : fits case842 = true := by decide +kernel
noncomputable def frame843 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 18, changes := [(348, true), (322, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (302816, 297971), numericProof := 76676, slack := 1}
noncomputable def case843 : PhysicalCase := ⟨2,296,.south,.push 322 (.stay 348),frame843⟩
theorem frame843_checked : CountedLocalCaseData.check data frame843 = true := by decide +kernel
theorem case843_fitted : fits case843 = true := by decide +kernel
noncomputable def frame844 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 18, changes := [(319, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832853, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341485, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (308429, 378143), numericProof := 76677, slack := 0}
noncomputable def case844 : PhysicalCase := ⟨2,371,.north,.push 345 (.stay 319),frame844⟩
theorem frame844_checked : CountedLocalCaseData.check data frame844 = true := by decide +kernel
theorem case844_fitted : fits case844 = true := by decide +kernel
noncomputable def frame845 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 18, changes := [(371, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832853, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341485, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (314054, 378150), numericProof := 76678, slack := 2}
noncomputable def case845 : PhysicalCase := ⟨2,319,.south,.push 345 (.stay 371),frame845⟩
theorem frame845_checked : CountedLocalCaseData.check data frame845 = true := by decide +kernel
theorem case845_fitted : fits case845 = true := by decide +kernel
noncomputable def frame846 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 18, changes := [(322, true), (348, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (318891, 314055), numericProof := 76679, slack := 1}
noncomputable def case846 : PhysicalCase := ⟨2,374,.north,.push 348 (.stay 322),frame846⟩
theorem frame846_checked : CountedLocalCaseData.check data frame846 = true := by decide +kernel
theorem case846_fitted : fits case846 = true := by decide +kernel
noncomputable def frame847 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 18, changes := [(374, true), (348, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (323752, 318892), numericProof := 76679, slack := 1}
noncomputable def case847 : PhysicalCase := ⟨2,322,.south,.push 348 (.stay 374),frame847⟩
theorem frame847_checked : CountedLocalCaseData.check data frame847 = true := by decide +kernel
theorem case847_fitted : fits case847 = true := by decide +kernel
noncomputable def frame848 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 18, changes := [(345, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832853, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341492, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (329389, 378157), numericProof := 76680, slack := 0}
noncomputable def case848 : PhysicalCase := ⟨2,397,.north,.push 371 (.stay 345),frame848⟩
theorem frame848_checked : CountedLocalCaseData.check data frame848 = true := by decide +kernel
theorem case848_fitted : fits case848 = true := by decide +kernel
noncomputable def frame849 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 18, changes := [(397, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832853, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341492, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (335039, 378164), numericProof := 76681, slack := 2}
noncomputable def case849 : PhysicalCase := ⟨2,345,.south,.push 371 (.stay 397),frame849⟩
theorem frame849_checked : CountedLocalCaseData.check data frame849 = true := by decide +kernel
theorem case849_fitted : fits case849 = true := by decide +kernel
noncomputable def frame850 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 18, changes := [(372, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832853, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 5834511, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341499, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341506, updateProofs := some (340681, 378171), numericProof := 76682, slack := 2}
noncomputable def case850 : PhysicalCase := ⟨2,370,.east,.push 371 (.stay 372),frame850⟩
theorem frame850_checked : CountedLocalCaseData.check data frame850 = true := by decide +kernel
theorem case850_fitted : fits case850 = true := by decide +kernel
noncomputable def frame851 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 18, changes := [(370, true), (371, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832853, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (346314, 378178), numericProof := 76683, slack := 2}
noncomputable def case851 : PhysicalCase := ⟨2,372,.west,.push 371 (.stay 370),frame851⟩
theorem frame851_checked : CountedLocalCaseData.check data frame851 = true := by decide +kernel
theorem case851_fitted : fits case851 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
