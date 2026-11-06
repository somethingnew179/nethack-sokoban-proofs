import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame792 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 18, changes := [(239, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832847, afterBeta := 5439691, afterBonus := 5832850, preBeta := 5439691, preBonus := 5834480, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341223, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341230, updateProofs := some (147813, 377905), numericProof := 76618, slack := 2}
noncomputable def case792 : PhysicalCase := ⟨2,237,.east,.push 238 (.stay 239),frame792⟩
theorem frame792_checked : CountedLocalCaseData.check data frame792 = true := by decide +kernel
theorem case792_fitted : fits case792 = true := by decide +kernel
noncomputable def frame793 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 18, changes := [(237, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832852, afterBeta := 5439691, afterBonus := 5832850, preBeta := 5439691, preBonus := 5834483, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341237, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341241, updateProofs := some (148494, 377912), numericProof := 76619, slack := 2}
noncomputable def case793 : PhysicalCase := ⟨2,239,.west,.push 238 (.stay 237),frame793⟩
theorem frame793_checked : CountedLocalCaseData.check data frame793 = true := by decide +kernel
theorem case793_fitted : fits case793 = true := by decide +kernel
noncomputable def frame794 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 18, changes := [(213, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832849, afterBeta := 5439691, afterBonus := 5832852, preBeta := 5439691, preBonus := 5834485, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341248, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341255, updateProofs := some (150523, 377919), numericProof := 76620, slack := 0}
noncomputable def case794 : PhysicalCase := ⟨2,265,.north,.push 239 (.stay 213),frame794⟩
theorem frame794_checked : CountedLocalCaseData.check data frame794 = true := by decide +kernel
theorem case794_fitted : fits case794 = true := by decide +kernel
noncomputable def frame795 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 18, changes := [(265, true), (239, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832852, preBeta := 5439691, preBonus := 5834486, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341262, updateProofs := some (152932, 377926), numericProof := 76621, slack := 2}
noncomputable def case795 : PhysicalCase := ⟨2,213,.south,.push 239 (.stay 265),frame795⟩
theorem frame795_checked : CountedLocalCaseData.check data frame795 = true := by decide +kernel
theorem case795_fitted : fits case795 = true := by decide +kernel
noncomputable def frame796 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 18, changes := [(218, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (157267, 152933), numericProof := 76622, slack := 0}
noncomputable def case796 : PhysicalCase := ⟨2,270,.north,.push 244 (.stay 218),frame796⟩
theorem frame796_checked : CountedLocalCaseData.check data frame796 = true := by decide +kernel
theorem case796_fitted : fits case796 = true := by decide +kernel
noncomputable def frame797 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 18, changes := [(270, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (161757, 157268), numericProof := 76623, slack := 2}
noncomputable def case797 : PhysicalCase := ⟨2,218,.south,.push 244 (.stay 270),frame797⟩
theorem frame797_checked : CountedLocalCaseData.check data frame797 = true := by decide +kernel
theorem case797_fitted : fits case797 = true := by decide +kernel
noncomputable def frame798 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 18, changes := [(219, true), (245, false)], beforeBeta := 5439701, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 426739, restrictionBeforeBonus := 3, restrictionAfterBeta := 422199, restrictionAfterBonus := 3, updateProofs := some (166105, 161758), numericProof := 76624, slack := 0}
noncomputable def case798 : PhysicalCase := ⟨2,271,.north,.push 245 (.stay 219),frame798⟩
theorem frame798_checked : CountedLocalCaseData.check data frame798 = true := by decide +kernel
theorem case798_fitted : fits case798 = true := by decide +kernel
noncomputable def frame799 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 18, changes := [(271, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5441377, preBonus := 0, restrictionBeforeBeta := 422199, restrictionBeforeBonus := 3, restrictionAfterBeta := 1116377, restrictionAfterBonus := 3, updateProofs := some (170833, 166106), numericProof := 76625, slack := 1}
noncomputable def case799 : PhysicalCase := ⟨2,219,.south,.push 245 (.stay 271),frame799⟩
theorem frame799_checked : CountedLocalCaseData.check data frame799 = true := by decide +kernel
theorem case799_fitted : fits case799 = true := by decide +kernel
noncomputable def frame800 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 18, changes := [(246, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (175422, 170834), numericProof := 76626, slack := 1}
noncomputable def case800 : PhysicalCase := ⟨2,244,.east,.push 245 (.stay 246),frame800⟩
theorem frame800_checked : CountedLocalCaseData.check data frame800 = true := by decide +kernel
theorem case800_fitted : fits case800 = true := by decide +kernel
noncomputable def frame801 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 18, changes := [(244, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (179950, 175423), numericProof := 76627, slack := 0}
noncomputable def case801 : PhysicalCase := ⟨2,246,.west,.push 245 (.stay 244),frame801⟩
theorem frame801_checked : CountedLocalCaseData.check data frame801 = true := by decide +kernel
theorem case801_fitted : fits case801 = true := by decide +kernel
noncomputable def frame802 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 18, changes := [(220, true), (246, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (181679, 179951), numericProof := 76628, slack := 1}
noncomputable def case802 : PhysicalCase := ⟨2,272,.north,.push 246 (.stay 220),frame802⟩
theorem frame802_checked : CountedLocalCaseData.check data frame802 = true := by decide +kernel
theorem case802_fitted : fits case802 = true := by decide +kernel
noncomputable def frame803 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 18, changes := [(272, true), (246, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (183534, 181680), numericProof := 76628, slack := 1}
noncomputable def case803 : PhysicalCase := ⟨2,220,.south,.push 246 (.stay 272),frame803⟩
theorem frame803_checked : CountedLocalCaseData.check data frame803 = true := by decide +kernel
theorem case803_fitted : fits case803 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
