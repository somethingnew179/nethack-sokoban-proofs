import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame792 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 19, changes := [(213, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832816, afterBeta := 5439691, afterBonus := 5832784, preBeta := 5439691, preBonus := 5834125, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337801, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337815, updateProofs := some (150523, 376651), numericProof := 75819, slack := 0}
noncomputable def case792 : PhysicalCase := ⟨1,265,.north,.push 239 (.stay 213),frame792⟩
theorem frame792_checked : CountedLocalCaseData.check data frame792 = true := by decide +kernel
theorem case792_fitted : fits case792 = true := by decide +kernel
noncomputable def frame793 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 19, changes := [(265, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832782, afterBeta := 5439691, afterBonus := 5832784, preBeta := 5439691, preBonus := 5834127, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337817, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337831, updateProofs := some (152932, 376665), numericProof := 75820, slack := 2}
noncomputable def case793 : PhysicalCase := ⟨1,213,.south,.push 239 (.stay 265),frame793⟩
theorem frame793_checked : CountedLocalCaseData.check data frame793 = true := by decide +kernel
theorem case793_fitted : fits case793 = true := by decide +kernel
noncomputable def frame794 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 19, changes := [(218, true), (244, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5834129, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337833, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337835, updateProofs := some (157267, 376667), numericProof := 75821, slack := 0}
noncomputable def case794 : PhysicalCase := ⟨1,270,.north,.push 244 (.stay 218),frame794⟩
theorem frame794_checked : CountedLocalCaseData.check data frame794 = true := by decide +kernel
theorem case794_fitted : fits case794 = true := by decide +kernel
noncomputable def frame795 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 19, changes := [(270, true), (244, false)], beforeBeta := 5439691, beforeBonus := 5832811, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337837, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (161757, 376669), numericProof := 75822, slack := 2}
noncomputable def case795 : PhysicalCase := ⟨1,218,.south,.push 244 (.stay 270),frame795⟩
theorem frame795_checked : CountedLocalCaseData.check data frame795 = true := by decide +kernel
theorem case795_fitted : fits case795 = true := by decide +kernel
noncomputable def frame796 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 19, changes := [(219, true), (245, false)], beforeBeta := 5439701, beforeBonus := 5832809, afterBeta := 5439691, afterBonus := 5832806, preBeta := 5439691, preBonus := 5834131, restrictionBeforeBeta := 426739, restrictionBeforeBonus := 1337839, restrictionAfterBeta := 422199, restrictionAfterBonus := 1337841, updateProofs := some (166105, 376671), numericProof := 75823, slack := 0}
noncomputable def case796 : PhysicalCase := ⟨1,271,.north,.push 245 (.stay 219),frame796⟩
theorem frame796_checked : CountedLocalCaseData.check data frame796 = true := by decide +kernel
theorem case796_fitted : fits case796 = true := by decide +kernel
noncomputable def frame797 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 19, changes := [(271, true), (245, false)], beforeBeta := 5439691, beforeBonus := 5832799, afterBeta := 5439691, afterBonus := 5832806, preBeta := 5441377, preBonus := 5834133, restrictionBeforeBeta := 422199, restrictionBeforeBonus := 1337843, restrictionAfterBeta := 1116377, restrictionAfterBonus := 1337845, updateProofs := some (170833, 376673), numericProof := 75827, slack := 1}
noncomputable def case797 : PhysicalCase := ⟨1,219,.south,.push 245 (.stay 271),frame797⟩
theorem frame797_checked : CountedLocalCaseData.check data frame797 = true := by decide +kernel
theorem case797_fitted : fits case797 = true := by decide +kernel
noncomputable def frame798 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 19, changes := [(246, true), (245, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832806, preBeta := 5439691, preBonus := 5834136, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337847, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337849, updateProofs := some (175422, 376675), numericProof := 75828, slack := 1}
noncomputable def case798 : PhysicalCase := ⟨1,244,.east,.push 245 (.stay 246),frame798⟩
theorem frame798_checked : CountedLocalCaseData.check data frame798 = true := by decide +kernel
theorem case798_fitted : fits case798 = true := by decide +kernel
noncomputable def frame799 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 19, changes := [(244, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832806, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (179950, 376677), numericProof := 75829, slack := 0}
noncomputable def case799 : PhysicalCase := ⟨1,246,.west,.push 245 (.stay 244),frame799⟩
theorem frame799_checked : CountedLocalCaseData.check data frame799 = true := by decide +kernel
theorem case799_fitted : fits case799 = true := by decide +kernel
noncomputable def frame800 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 19, changes := [(220, true), (246, false)], beforeBeta := 5439691, beforeBonus := 5832810, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337851, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (181679, 179951), numericProof := 75830, slack := 1}
noncomputable def case800 : PhysicalCase := ⟨1,272,.north,.push 246 (.stay 220),frame800⟩
theorem frame800_checked : CountedLocalCaseData.check data frame800 = true := by decide +kernel
theorem case800_fitted : fits case800 = true := by decide +kernel
noncomputable def frame801 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 19, changes := [(272, true), (246, false)], beforeBeta := 5439691, beforeBonus := 5832804, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337853, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (183534, 181680), numericProof := 75831, slack := 1}
noncomputable def case801 : PhysicalCase := ⟨1,220,.south,.push 246 (.stay 272),frame801⟩
theorem frame801_checked : CountedLocalCaseData.check data frame801 = true := by decide +kernel
theorem case801_fitted : fits case801 = true := by decide +kernel
noncomputable def frame802 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 19, changes := [(236, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337874, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (184959, 376698), numericProof := 75832, slack := 0}
noncomputable def case802 : PhysicalCase := ⟨1,288,.north,.push 262 (.stay 236),frame802⟩
theorem frame802_checked : CountedLocalCaseData.check data frame802 = true := by decide +kernel
theorem case802_fitted : fits case802 = true := by decide +kernel
noncomputable def frame803 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 19, changes := [(288, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337874, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (186510, 376719), numericProof := 75833, slack := 7}
noncomputable def case803 : PhysicalCase := ⟨1,236,.south,.push 262 (.stay 288),frame803⟩
theorem frame803_checked : CountedLocalCaseData.check data frame803 = true := by decide +kernel
theorem case803_fitted : fits case803 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
