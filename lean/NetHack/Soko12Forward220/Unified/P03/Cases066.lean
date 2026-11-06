import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame792 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 17, changes := [(212, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832878, afterBeta := 5439691, afterBonus := 5832875, preBeta := 5439691, preBonus := 5834791, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343083, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343086, updateProofs := some (146345, 378428), numericProof := 77206, slack := 0}
noncomputable def case792 : PhysicalCase := ⟨3,264,.north,.push 238 (.stay 212),frame792⟩
theorem frame792_checked : CountedLocalCaseData.check data frame792 = true := by decide +kernel
theorem case792_fitted : fits case792 = true := by decide +kernel
noncomputable def frame793 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 17, changes := [(264, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832870, afterBeta := 5439691, afterBonus := 5832875, preBeta := 5439691, preBonus := 5834793, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343090, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343093, updateProofs := some (147122, 378432), numericProof := 77207, slack := 2}
noncomputable def case793 : PhysicalCase := ⟨3,212,.south,.push 238 (.stay 264),frame793⟩
theorem frame793_checked : CountedLocalCaseData.check data frame793 = true := by decide +kernel
theorem case793_fitted : fits case793 = true := by decide +kernel
noncomputable def frame794 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 17, changes := [(239, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832872, afterBeta := 5439691, afterBonus := 5832875, preBeta := 5439691, preBonus := 5834796, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343097, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343101, updateProofs := some (147813, 378436), numericProof := 77208, slack := 2}
noncomputable def case794 : PhysicalCase := ⟨3,237,.east,.push 238 (.stay 239),frame794⟩
theorem frame794_checked : CountedLocalCaseData.check data frame794 = true := by decide +kernel
theorem case794_fitted : fits case794 = true := by decide +kernel
noncomputable def frame795 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 17, changes := [(237, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832876, afterBeta := 5439691, afterBonus := 5832875, preBeta := 5439691, preBonus := 5834799, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343105, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343108, updateProofs := some (148494, 378440), numericProof := 77209, slack := 2}
noncomputable def case795 : PhysicalCase := ⟨3,239,.west,.push 238 (.stay 237),frame795⟩
theorem frame795_checked : CountedLocalCaseData.check data frame795 = true := by decide +kernel
theorem case795_fitted : fits case795 = true := by decide +kernel
noncomputable def frame796 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 17, changes := [(213, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832879, afterBeta := 5439691, afterBonus := 5832876, preBeta := 5439691, preBonus := 5834801, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343112, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343116, updateProofs := some (150523, 378444), numericProof := 77210, slack := 0}
noncomputable def case796 : PhysicalCase := ⟨3,265,.north,.push 239 (.stay 213),frame796⟩
theorem frame796_checked : CountedLocalCaseData.check data frame796 = true := by decide +kernel
theorem case796_fitted : fits case796 = true := by decide +kernel
noncomputable def frame797 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 17, changes := [(265, true), (239, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832876, preBeta := 5439691, preBonus := 5834802, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343120, updateProofs := some (152932, 378448), numericProof := 77211, slack := 2}
noncomputable def case797 : PhysicalCase := ⟨3,213,.south,.push 239 (.stay 265),frame797⟩
theorem frame797_checked : CountedLocalCaseData.check data frame797 = true := by decide +kernel
theorem case797_fitted : fits case797 = true := by decide +kernel
noncomputable def frame798 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 17, changes := [(218, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (157267, 152933), numericProof := 77212, slack := 0}
noncomputable def case798 : PhysicalCase := ⟨3,270,.north,.push 244 (.stay 218),frame798⟩
theorem frame798_checked : CountedLocalCaseData.check data frame798 = true := by decide +kernel
theorem case798_fitted : fits case798 = true := by decide +kernel
noncomputable def frame799 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 17, changes := [(270, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (161757, 157268), numericProof := 77213, slack := 2}
noncomputable def case799 : PhysicalCase := ⟨3,218,.south,.push 244 (.stay 270),frame799⟩
theorem frame799_checked : CountedLocalCaseData.check data frame799 = true := by decide +kernel
theorem case799_fitted : fits case799 = true := by decide +kernel
noncomputable def frame800 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 17, changes := [(219, true), (245, false)], beforeBeta := 5439701, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 426739, restrictionBeforeBonus := 3, restrictionAfterBeta := 422199, restrictionAfterBonus := 3, updateProofs := some (166105, 161758), numericProof := 77214, slack := 0}
noncomputable def case800 : PhysicalCase := ⟨3,271,.north,.push 245 (.stay 219),frame800⟩
theorem frame800_checked : CountedLocalCaseData.check data frame800 = true := by decide +kernel
theorem case800_fitted : fits case800 = true := by decide +kernel
noncomputable def frame801 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 17, changes := [(271, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5441377, preBonus := 0, restrictionBeforeBeta := 422199, restrictionBeforeBonus := 3, restrictionAfterBeta := 1116377, restrictionAfterBonus := 3, updateProofs := some (170833, 166106), numericProof := 77215, slack := 1}
noncomputable def case801 : PhysicalCase := ⟨3,219,.south,.push 245 (.stay 271),frame801⟩
theorem frame801_checked : CountedLocalCaseData.check data frame801 = true := by decide +kernel
theorem case801_fitted : fits case801 = true := by decide +kernel
noncomputable def frame802 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 17, changes := [(246, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (175422, 170834), numericProof := 77216, slack := 1}
noncomputable def case802 : PhysicalCase := ⟨3,244,.east,.push 245 (.stay 246),frame802⟩
theorem frame802_checked : CountedLocalCaseData.check data frame802 = true := by decide +kernel
theorem case802_fitted : fits case802 = true := by decide +kernel
noncomputable def frame803 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 17, changes := [(244, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (179950, 175423), numericProof := 77217, slack := 0}
noncomputable def case803 : PhysicalCase := ⟨3,246,.west,.push 245 (.stay 244),frame803⟩
theorem frame803_checked : CountedLocalCaseData.check data frame803 = true := by decide +kernel
theorem case803_fitted : fits case803 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
