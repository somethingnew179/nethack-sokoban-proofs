import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame804 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 17, changes := [(220, true), (246, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (181679, 179951), numericProof := 77218, slack := 1}
noncomputable def case804 : PhysicalCase := ⟨3,272,.north,.push 246 (.stay 220),frame804⟩
theorem frame804_checked : CountedLocalCaseData.check data frame804 = true := by decide +kernel
theorem case804_fitted : fits case804 = true := by decide +kernel
noncomputable def frame805 : CountedLocalCase.Frame := {bindings := [(220, false), (246, true), (272, false)], budget := 17, changes := [(272, true), (246, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (183534, 181680), numericProof := 77218, slack := 1}
noncomputable def case805 : PhysicalCase := ⟨3,220,.south,.push 246 (.stay 272),frame805⟩
theorem frame805_checked : CountedLocalCaseData.check data frame805 = true := by decide +kernel
theorem case805_fitted : fits case805 = true := by decide +kernel
noncomputable def frame806 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 17, changes := [(236, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343124, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (184959, 378452), numericProof := 77219, slack := 0}
noncomputable def case806 : PhysicalCase := ⟨3,288,.north,.push 262 (.stay 236),frame806⟩
theorem frame806_checked : CountedLocalCaseData.check data frame806 = true := by decide +kernel
theorem case806_fitted : fits case806 = true := by decide +kernel
noncomputable def frame807 : CountedLocalCase.Frame := {bindings := [(236, false), (262, true), (288, false)], budget := 17, changes := [(288, true), (262, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832873, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343124, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (186510, 378456), numericProof := 77220, slack := 7}
noncomputable def case807 : PhysicalCase := ⟨3,236,.south,.push 262 (.stay 288),frame807⟩
theorem frame807_checked : CountedLocalCaseData.check data frame807 = true := by decide +kernel
theorem case807_fitted : fits case807 = true := by decide +kernel
noncomputable def frame808 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 17, changes := [(237, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832877, preBeta := 5439691, preBonus := 5834803, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343128, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343131, updateProofs := some (188005, 378460), numericProof := 77224, slack := 0}
noncomputable def case808 : PhysicalCase := ⟨3,289,.north,.push 263 (.stay 237),frame808⟩
theorem frame808_checked : CountedLocalCaseData.check data frame808 = true := by decide +kernel
theorem case808_fitted : fits case808 = true := by decide +kernel
noncomputable def frame809 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 17, changes := [(289, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832872, afterBeta := 5439691, afterBonus := 5832877, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343134, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (189522, 378464), numericProof := 77225, slack := 4}
noncomputable def case809 : PhysicalCase := ⟨3,237,.south,.push 263 (.stay 289),frame809⟩
theorem frame809_checked : CountedLocalCaseData.check data frame809 = true := by decide +kernel
theorem case809_fitted : fits case809 = true := by decide +kernel
noncomputable def frame810 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 17, changes := [(264, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832877, preBeta := 5439691, preBonus := 5834806, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343138, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343141, updateProofs := some (191021, 378468), numericProof := 77229, slack := 0}
noncomputable def case810 : PhysicalCase := ⟨3,262,.east,.push 263 (.stay 264),frame810⟩
theorem frame810_checked : CountedLocalCaseData.check data frame810 = true := by decide +kernel
theorem case810_fitted : fits case810 = true := by decide +kernel
noncomputable def frame811 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 17, changes := [(262, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832878, afterBeta := 5439691, afterBonus := 5832877, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343144, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (192504, 378472), numericProof := 77230, slack := 2}
noncomputable def case811 : PhysicalCase := ⟨3,264,.west,.push 263 (.stay 262),frame811⟩
theorem frame811_checked : CountedLocalCaseData.check data frame811 = true := by decide +kernel
theorem case811_fitted : fits case811 = true := by decide +kernel
noncomputable def frame812 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 17, changes := [(238, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832878, preBeta := 5439691, preBonus := 5834809, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343148, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343152, updateProofs := some (194360, 378476), numericProof := 77235, slack := 0}
noncomputable def case812 : PhysicalCase := ⟨3,290,.north,.push 264 (.stay 238),frame812⟩
theorem frame812_checked : CountedLocalCaseData.check data frame812 = true := by decide +kernel
theorem case812_fitted : fits case812 = true := by decide +kernel
noncomputable def frame813 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 17, changes := [(290, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832875, afterBeta := 5439691, afterBonus := 5832878, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343156, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (196259, 378480), numericProof := 77236, slack := 4}
noncomputable def case813 : PhysicalCase := ⟨3,238,.south,.push 264 (.stay 290),frame813⟩
theorem frame813_checked : CountedLocalCaseData.check data frame813 = true := by decide +kernel
theorem case813_fitted : fits case813 = true := by decide +kernel
noncomputable def frame814 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 17, changes := [(265, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832877, afterBeta := 5439691, afterBonus := 5832878, preBeta := 5439691, preBonus := 5834812, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343160, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343164, updateProofs := some (198116, 378484), numericProof := 77237, slack := 2}
noncomputable def case814 : PhysicalCase := ⟨3,263,.east,.push 264 (.stay 265),frame814⟩
theorem frame814_checked : CountedLocalCaseData.check data frame814 = true := by decide +kernel
theorem case814_fitted : fits case814 = true := by decide +kernel
noncomputable def frame815 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 17, changes := [(263, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832879, afterBeta := 5439691, afterBonus := 5832878, preBeta := 5439691, preBonus := 5834815, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343168, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343171, updateProofs := some (199972, 378488), numericProof := 77238, slack := 2}
noncomputable def case815 : PhysicalCase := ⟨3,265,.west,.push 264 (.stay 263),frame815⟩
theorem frame815_checked : CountedLocalCaseData.check data frame815 = true := by decide +kernel
theorem case815_fitted : fits case815 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
