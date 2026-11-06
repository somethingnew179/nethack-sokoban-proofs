import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame804 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 16, changes := [(246, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (175422, 170834), numericProof := 77757, slack := 1}
noncomputable def case804 : PhysicalCase := ⟨4,244,.east,.push 245 (.stay 246),frame804⟩
theorem frame804_checked : CountedLocalCaseData.check data frame804 = true := by decide +kernel
theorem case804_fitted : fits case804 = true := by decide +kernel
noncomputable def frame805 : CountedLocalCase.Frame := {bindings := [(244, false), (245, true), (246, false)], budget := 16, changes := [(244, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (179950, 175423), numericProof := 77758, slack := 0}
noncomputable def case805 : PhysicalCase := ⟨4,246,.west,.push 245 (.stay 244),frame805⟩
theorem frame805_checked : CountedLocalCaseData.check data frame805 = true := by decide +kernel
theorem case805_fitted : fits case805 = true := by decide +kernel
noncomputable def frame806 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 16, changes := [(220, true), (246, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (181679, 179951), numericProof := 77759, slack := 1}
noncomputable def case806 : PhysicalCase := ⟨4,272,.north,.push 246 (.stay 220),frame806⟩
theorem frame806_checked : CountedLocalCaseData.check data frame806 = true := by decide +kernel
theorem case806_fitted : fits case806 = true := by decide +kernel
noncomputable def frame807 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 16, changes := [(272, true), (246, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (183534, 181680), numericProof := 77759, slack := 1}
noncomputable def case807 : PhysicalCase := ⟨4,220,.south,.push 246 (.stay 272),frame807⟩
theorem frame807_checked : CountedLocalCaseData.check data frame807 = true := by decide +kernel
theorem case807_fitted : fits case807 = true := by decide +kernel
noncomputable def frame808 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 16, changes := [(236, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344444, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (184959, 378797), numericProof := 77760, slack := 0}
noncomputable def case808 : PhysicalCase := ⟨4,288,.north,.push 262 (.stay 236),frame808⟩
theorem frame808_checked : CountedLocalCaseData.check data frame808 = true := by decide +kernel
theorem case808_fitted : fits case808 = true := by decide +kernel
noncomputable def frame809 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 16, changes := [(288, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832901, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344444, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (186510, 378800), numericProof := 77761, slack := 7}
noncomputable def case809 : PhysicalCase := ⟨4,236,.south,.push 262 (.stay 288),frame809⟩
theorem frame809_checked : CountedLocalCaseData.check data frame809 = true := by decide +kernel
theorem case809_fitted : fits case809 = true := by decide +kernel
noncomputable def frame810 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 16, changes := [(237, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832902, preBeta := 5439691, preBonus := 5835062, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344447, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344449, updateProofs := some (188005, 378803), numericProof := 77762, slack := 0}
noncomputable def case810 : PhysicalCase := ⟨4,289,.north,.push 263 (.stay 237),frame810⟩
theorem frame810_checked : CountedLocalCaseData.check data frame810 = true := by decide +kernel
theorem case810_fitted : fits case810 = true := by decide +kernel
noncomputable def frame811 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 16, changes := [(289, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832900, afterBeta := 5439691, afterBonus := 5832902, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344451, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (189522, 378806), numericProof := 77763, slack := 4}
noncomputable def case811 : PhysicalCase := ⟨4,237,.south,.push 263 (.stay 289),frame811⟩
theorem frame811_checked : CountedLocalCaseData.check data frame811 = true := by decide +kernel
theorem case811_fitted : fits case811 = true := by decide +kernel
noncomputable def frame812 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 16, changes := [(264, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832902, preBeta := 5439691, preBonus := 5835078, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344454, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344456, updateProofs := some (191021, 378809), numericProof := 77764, slack := 0}
noncomputable def case812 : PhysicalCase := ⟨4,262,.east,.push 263 (.stay 264),frame812⟩
theorem frame812_checked : CountedLocalCaseData.check data frame812 = true := by decide +kernel
theorem case812_fitted : fits case812 = true := by decide +kernel
noncomputable def frame813 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 16, changes := [(262, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832905, afterBeta := 5439691, afterBonus := 5832902, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344458, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (192504, 378812), numericProof := 77765, slack := 2}
noncomputable def case813 : PhysicalCase := ⟨4,264,.west,.push 263 (.stay 262),frame813⟩
theorem frame813_checked : CountedLocalCaseData.check data frame813 = true := by decide +kernel
theorem case813_fitted : fits case813 = true := by decide +kernel
noncomputable def frame814 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 16, changes := [(238, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832905, preBeta := 5439691, preBonus := 5835080, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344461, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344464, updateProofs := some (194360, 378815), numericProof := 77769, slack := 0}
noncomputable def case814 : PhysicalCase := ⟨4,290,.north,.push 264 (.stay 238),frame814⟩
theorem frame814_checked : CountedLocalCaseData.check data frame814 = true := by decide +kernel
theorem case814_fitted : fits case814 = true := by decide +kernel
noncomputable def frame815 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 16, changes := [(290, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832903, afterBeta := 5439691, afterBonus := 5832905, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344467, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (196259, 378818), numericProof := 77770, slack := 4}
noncomputable def case815 : PhysicalCase := ⟨4,238,.south,.push 264 (.stay 290),frame815⟩
theorem frame815_checked : CountedLocalCaseData.check data frame815 = true := by decide +kernel
theorem case815_fitted : fits case815 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
