import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame804 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 18, changes := [(236, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341269, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (184959, 377933), numericProof := 76629, slack := 0}
noncomputable def case804 : PhysicalCase := ⟨2,288,.north,.push 262 (.stay 236),frame804⟩
theorem frame804_checked : CountedLocalCaseData.check data frame804 = true := by decide +kernel
theorem case804_fitted : fits case804 = true := by decide +kernel
noncomputable def frame805 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 18, changes := [(288, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832845, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341269, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (186510, 377940), numericProof := 76630, slack := 7}
noncomputable def case805 : PhysicalCase := ⟨2,236,.south,.push 262 (.stay 288),frame805⟩
theorem frame805_checked : CountedLocalCaseData.check data frame805 = true := by decide +kernel
theorem case805_fitted : fits case805 = true := by decide +kernel
noncomputable def frame806 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 18, changes := [(237, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832846, preBeta := 5439691, preBonus := 5834487, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341276, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341280, updateProofs := some (188005, 377947), numericProof := 76635, slack := 0}
noncomputable def case806 : PhysicalCase := ⟨2,289,.north,.push 263 (.stay 237),frame806⟩
theorem frame806_checked : CountedLocalCaseData.check data frame806 = true := by decide +kernel
theorem case806_fitted : fits case806 = true := by decide +kernel
noncomputable def frame807 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 18, changes := [(289, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832847, afterBeta := 5439691, afterBonus := 5832846, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341284, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (189522, 377954), numericProof := 76636, slack := 4}
noncomputable def case807 : PhysicalCase := ⟨2,237,.south,.push 263 (.stay 289),frame807⟩
theorem frame807_checked : CountedLocalCaseData.check data frame807 = true := by decide +kernel
theorem case807_fitted : fits case807 = true := by decide +kernel
noncomputable def frame808 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 18, changes := [(264, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832846, preBeta := 5439691, preBonus := 5834490, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341291, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341295, updateProofs := some (191021, 377961), numericProof := 76641, slack := 0}
noncomputable def case808 : PhysicalCase := ⟨2,262,.east,.push 263 (.stay 264),frame808⟩
theorem frame808_checked : CountedLocalCaseData.check data frame808 = true := by decide +kernel
theorem case808_fitted : fits case808 = true := by decide +kernel
noncomputable def frame809 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 18, changes := [(262, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832848, afterBeta := 5439691, afterBonus := 5832846, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341299, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (192504, 377968), numericProof := 76642, slack := 2}
noncomputable def case809 : PhysicalCase := ⟨2,264,.west,.push 263 (.stay 262),frame809⟩
theorem frame809_checked : CountedLocalCaseData.check data frame809 = true := by decide +kernel
theorem case809_fitted : fits case809 = true := by decide +kernel
noncomputable def frame810 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 18, changes := [(238, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832848, preBeta := 5439691, preBonus := 5834493, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341306, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341313, updateProofs := some (194360, 377975), numericProof := 76648, slack := 0}
noncomputable def case810 : PhysicalCase := ⟨2,290,.north,.push 264 (.stay 238),frame810⟩
theorem frame810_checked : CountedLocalCaseData.check data frame810 = true := by decide +kernel
theorem case810_fitted : fits case810 = true := by decide +kernel
noncomputable def frame811 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 18, changes := [(290, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832850, afterBeta := 5439691, afterBonus := 5832848, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341320, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (196259, 377982), numericProof := 76649, slack := 4}
noncomputable def case811 : PhysicalCase := ⟨2,238,.south,.push 264 (.stay 290),frame811⟩
theorem frame811_checked : CountedLocalCaseData.check data frame811 = true := by decide +kernel
theorem case811_fitted : fits case811 = true := by decide +kernel
noncomputable def frame812 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 18, changes := [(265, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832846, afterBeta := 5439691, afterBonus := 5832848, preBeta := 5439691, preBonus := 5834497, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341327, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341334, updateProofs := some (198116, 377989), numericProof := 76650, slack := 2}
noncomputable def case812 : PhysicalCase := ⟨2,263,.east,.push 264 (.stay 265),frame812⟩
theorem frame812_checked : CountedLocalCaseData.check data frame812 = true := by decide +kernel
theorem case812_fitted : fits case812 = true := by decide +kernel
noncomputable def frame813 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 18, changes := [(263, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832849, afterBeta := 5439691, afterBonus := 5832848, preBeta := 5439691, preBonus := 5834500, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341341, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341345, updateProofs := some (199972, 377996), numericProof := 76651, slack := 2}
noncomputable def case813 : PhysicalCase := ⟨2,265,.west,.push 264 (.stay 263),frame813⟩
theorem frame813_checked : CountedLocalCaseData.check data frame813 = true := by decide +kernel
theorem case813_fitted : fits case813 = true := by decide +kernel
noncomputable def frame814 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 18, changes := [(239, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832845, afterBeta := 5439691, afterBonus := 5832849, preBeta := 5439691, preBonus := 5834502, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341352, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341359, updateProofs := some (201896, 378003), numericProof := 76652, slack := 0}
noncomputable def case814 : PhysicalCase := ⟨2,291,.north,.push 265 (.stay 239),frame814⟩
theorem frame814_checked : CountedLocalCaseData.check data frame814 = true := by decide +kernel
theorem case814_fitted : fits case814 = true := by decide +kernel
noncomputable def frame815 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 18, changes := [(291, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832852, afterBeta := 5439691, afterBonus := 5832849, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341366, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (203881, 378010), numericProof := 76653, slack := 2}
noncomputable def case815 : PhysicalCase := ⟨2,239,.south,.push 265 (.stay 291),frame815⟩
theorem frame815_checked : CountedLocalCaseData.check data frame815 = true := by decide +kernel
theorem case815_fitted : fits case815 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
