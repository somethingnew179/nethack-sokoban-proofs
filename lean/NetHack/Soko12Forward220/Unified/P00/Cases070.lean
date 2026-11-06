import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame840 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 20, changes := [(319, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832705, afterBeta := 5439691, afterBonus := 5832706, preBeta := 5439691, preBonus := 5833605, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1280051, restrictionAfterBeta := 8531, restrictionAfterBonus := 1284468, updateProofs := some (308429, 308352), numericProof := 74464, slack := 0}
noncomputable def case840 : PhysicalCase := ⟨0,371,.north,.push 345 (.stay 319),frame840⟩
theorem frame840_checked : CountedLocalCaseData.check data frame840 = true := by decide +kernel
theorem case840_fitted : fits case840 = true := by decide +kernel
noncomputable def frame841 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 20, changes := [(371, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832708, afterBeta := 5439691, afterBonus := 5832706, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1289099, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (314054, 313977), numericProof := 74465, slack := 2}
noncomputable def case841 : PhysicalCase := ⟨0,319,.south,.push 345 (.stay 371),frame841⟩
theorem frame841_checked : CountedLocalCaseData.check data frame841 = true := by decide +kernel
theorem case841_fitted : fits case841 = true := by decide +kernel
noncomputable def frame842 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 20, changes := [(322, true), (348, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1293867, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (318891, 318814), numericProof := 74466, slack := 1}
noncomputable def case842 : PhysicalCase := ⟨0,374,.north,.push 348 (.stay 322),frame842⟩
theorem frame842_checked : CountedLocalCaseData.check data frame842 = true := by decide +kernel
theorem case842_fitted : fits case842 = true := by decide +kernel
noncomputable def frame843 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 20, changes := [(374, true), (348, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1293867, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (323752, 323675), numericProof := 74466, slack := 1}
noncomputable def case843 : PhysicalCase := ⟨0,322,.south,.push 348 (.stay 374),frame843⟩
theorem frame843_checked : CountedLocalCaseData.check data frame843 = true := by decide +kernel
theorem case843_fitted : fits case843 = true := by decide +kernel
noncomputable def frame844 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 20, changes := [(345, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832704, afterBeta := 5439691, afterBonus := 5832705, preBeta := 5439691, preBonus := 5833607, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1299429, restrictionAfterBeta := 8531, restrictionAfterBonus := 1303855, updateProofs := some (329389, 329312), numericProof := 74597, slack := 0}
noncomputable def case844 : PhysicalCase := ⟨0,397,.north,.push 371 (.stay 345),frame844⟩
theorem frame844_checked : CountedLocalCaseData.check data frame844 = true := by decide +kernel
theorem case844_fitted : fits case844 = true := by decide +kernel
noncomputable def frame845 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 20, changes := [(397, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832706, afterBeta := 5439691, afterBonus := 5832705, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1308519, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (335039, 334962), numericProof := 74598, slack := 2}
noncomputable def case845 : PhysicalCase := ⟨0,345,.south,.push 371 (.stay 397),frame845⟩
theorem frame845_checked : CountedLocalCaseData.check data frame845 = true := by decide +kernel
theorem case845_fitted : fits case845 = true := by decide +kernel
noncomputable def frame846 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 20, changes := [(372, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832704, afterBeta := 5439691, afterBonus := 5832705, preBeta := 5439691, preBonus := 5833610, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1314081, restrictionAfterBeta := 8531, restrictionAfterBonus := 1314932, updateProofs := some (340681, 340604), numericProof := 74761, slack := 2}
noncomputable def case846 : PhysicalCase := ⟨0,370,.east,.push 371 (.stay 372),frame846⟩
theorem frame846_checked : CountedLocalCaseData.check data frame846 = true := by decide +kernel
theorem case846_fitted : fits case846 = true := by decide +kernel
noncomputable def frame847 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 20, changes := [(370, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832705, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1315096, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (346314, 346237), numericProof := 74762, slack := 2}
noncomputable def case847 : PhysicalCase := ⟨0,372,.west,.push 371 (.stay 370),frame847⟩
theorem frame847_checked : CountedLocalCaseData.check data frame847 = true := by decide +kernel
theorem case847_fitted : fits case847 = true := by decide +kernel
noncomputable def frame848 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 20, changes := [(373, true), (372, false)], beforeBeta := 5439691, beforeBonus := 5832705, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1320659, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (351172, 351095), numericProof := 74763, slack := 1}
noncomputable def case848 : PhysicalCase := ⟨0,371,.east,.push 372 (.stay 373),frame848⟩
theorem frame848_checked : CountedLocalCaseData.check data frame848 = true := by decide +kernel
theorem case848_fitted : fits case848 = true := by decide +kernel
noncomputable def frame849 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 20, changes := [(371, true), (372, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1320823, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (356024, 355947), numericProof := 74764, slack := 0}
noncomputable def case849 : PhysicalCase := ⟨0,373,.west,.push 372 (.stay 371),frame849⟩
theorem frame849_checked : CountedLocalCaseData.check data frame849 = true := by decide +kernel
theorem case849_fitted : fits case849 = true := by decide +kernel
noncomputable def frame850 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 20, changes := [(374, true), (373, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1325603, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (360885, 360808), numericProof := 74765, slack := 1}
noncomputable def case850 : PhysicalCase := ⟨0,372,.east,.push 373 (.stay 374),frame850⟩
theorem frame850_checked : CountedLocalCaseData.check data frame850 = true := by decide +kernel
theorem case850_fitted : fits case850 = true := by decide +kernel
noncomputable def frame851 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 20, changes := [(372, true), (373, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1325603, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (365740, 365663), numericProof := 74765, slack := 1}
noncomputable def case851 : PhysicalCase := ⟨0,374,.west,.push 373 (.stay 372),frame851⟩
theorem frame851_checked : CountedLocalCaseData.check data frame851 = true := by decide +kernel
theorem case851_fitted : fits case851 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
