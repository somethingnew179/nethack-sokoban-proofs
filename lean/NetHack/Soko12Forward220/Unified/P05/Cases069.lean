import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame828 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 15, changes := [(290, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345194, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (225168, 379057), numericProof := 78290, slack := 0}
noncomputable def case828 : PhysicalCase := ⟨5,288,.east,.push 289 (.stay 290),frame828⟩
theorem frame828_checked : CountedLocalCaseData.check data frame828 = true := by decide +kernel
theorem case828_fitted : fits case828 = true := by decide +kernel
noncomputable def frame829 : CountedLocalCase.Frame := {bindings := [(288, false), (289, true), (290, false)], budget := 15, changes := [(288, true), (289, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345194, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (226719, 379059), numericProof := 78291, slack := 5}
noncomputable def case829 : PhysicalCase := ⟨5,290,.west,.push 289 (.stay 288),frame829⟩
theorem frame829_checked : CountedLocalCaseData.check data frame829 = true := by decide +kernel
theorem case829_fitted : fits case829 = true := by decide +kernel
noncomputable def frame830 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 15, changes := [(291, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345196, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (228281, 379061), numericProof := 78292, slack := 0}
noncomputable def case830 : PhysicalCase := ⟨5,289,.east,.push 290 (.stay 291),frame830⟩
theorem frame830_checked : CountedLocalCaseData.check data frame830 = true := by decide +kernel
theorem case830_fitted : fits case830 = true := by decide +kernel
noncomputable def frame831 : CountedLocalCase.Frame := {bindings := [(289, false), (290, true), (291, false)], budget := 15, changes := [(289, true), (290, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345196, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (229835, 379063), numericProof := 78293, slack := 2}
noncomputable def case831 : PhysicalCase := ⟨5,291,.west,.push 290 (.stay 289),frame831⟩
theorem frame831_checked : CountedLocalCaseData.check data frame831 = true := by decide +kernel
theorem case831_fitted : fits case831 = true := by decide +kernel
noncomputable def frame832 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 15, changes := [(265, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 5835267, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345198, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345200, updateProofs := some (231551, 379065), numericProof := 78294, slack := 0}
noncomputable def case832 : PhysicalCase := ⟨5,317,.north,.push 291 (.stay 265),frame832⟩
theorem frame832_checked : CountedLocalCaseData.check data frame832 = true := by decide +kernel
theorem case832_fitted : fits case832 = true := by decide +kernel
noncomputable def frame833 : CountedLocalCase.Frame := {bindings := [(265, false), (291, true), (317, false)], budget := 15, changes := [(317, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832913, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345202, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (233281, 379067), numericProof := 78295, slack := 7}
noncomputable def case833 : PhysicalCase := ⟨5,265,.south,.push 291 (.stay 317),frame833⟩
theorem frame833_checked : CountedLocalCaseData.check data frame833 = true := by decide +kernel
theorem case833_fitted : fits case833 = true := by decide +kernel
noncomputable def frame834 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 15, changes := [(292, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345204, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (234997, 379069), numericProof := 78296, slack := 2}
noncomputable def case834 : PhysicalCase := ⟨5,290,.east,.push 291 (.stay 292),frame834⟩
theorem frame834_checked : CountedLocalCaseData.check data frame834 = true := by decide +kernel
theorem case834_fitted : fits case834 = true := by decide +kernel
noncomputable def frame835 : CountedLocalCase.Frame := {bindings := [(290, false), (291, true), (292, false)], budget := 15, changes := [(290, true), (291, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345204, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (236711, 379071), numericProof := 78296, slack := 2}
noncomputable def case835 : PhysicalCase := ⟨5,292,.west,.push 291 (.stay 290),frame835⟩
theorem frame835_checked : CountedLocalCaseData.check data frame835 = true := by decide +kernel
theorem case835_fitted : fits case835 = true := by decide +kernel
noncomputable def frame836 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 15, changes := [(293, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345206, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (241780, 379073), numericProof := 78297, slack := 2}
noncomputable def case836 : PhysicalCase := ⟨5,291,.east,.push 292 (.stay 293),frame836⟩
theorem frame836_checked : CountedLocalCaseData.check data frame836 = true := by decide +kernel
theorem case836_fitted : fits case836 = true := by decide +kernel
noncomputable def frame837 : CountedLocalCase.Frame := {bindings := [(291, false), (292, true), (293, false)], budget := 15, changes := [(291, true), (292, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345206, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (246843, 379075), numericProof := 78298, slack := 0}
noncomputable def case837 : PhysicalCase := ⟨5,293,.west,.push 292 (.stay 291),frame837⟩
theorem frame837_checked : CountedLocalCaseData.check data frame837 = true := by decide +kernel
theorem case837_fitted : fits case837 = true := by decide +kernel
noncomputable def frame838 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 15, changes := [(294, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345208, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (252384, 379077), numericProof := 78299, slack := 5}
noncomputable def case838 : PhysicalCase := ⟨5,292,.east,.push 293 (.stay 294),frame838⟩
theorem frame838_checked : CountedLocalCaseData.check data frame838 = true := by decide +kernel
theorem case838_fitted : fits case838 = true := by decide +kernel
noncomputable def frame839 : CountedLocalCase.Frame := {bindings := [(292, false), (293, true), (294, false)], budget := 15, changes := [(292, true), (293, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345208, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (257919, 379079), numericProof := 78300, slack := 0}
noncomputable def case839 : PhysicalCase := ⟨5,294,.west,.push 293 (.stay 292),frame839⟩
theorem frame839_checked : CountedLocalCaseData.check data frame839 = true := by decide +kernel
theorem case839_fitted : fits case839 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
