import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame804 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 19, changes := [(237, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832812, preBeta := 5439691, preBonus := 5834140, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337895, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337902, updateProofs := some (188005, 376740), numericProof := 75839, slack := 0}
noncomputable def case804 : PhysicalCase := ⟨1,289,.north,.push 263 (.stay 237),frame804⟩
theorem frame804_checked : CountedLocalCaseData.check data frame804 = true := by decide +kernel
theorem case804_fitted : fits case804 = true := by decide +kernel
noncomputable def frame805 : CountedLocalCase.Frame := {bindings := [(237, false), (263, true), (289, false)], budget := 19, changes := [(289, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832813, afterBeta := 5439691, afterBonus := 5832812, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337916, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (189522, 376761), numericProof := 75840, slack := 4}
noncomputable def case805 : PhysicalCase := ⟨1,237,.south,.push 263 (.stay 289),frame805⟩
theorem frame805_checked : CountedLocalCaseData.check data frame805 = true := by decide +kernel
theorem case805_fitted : fits case805 = true := by decide +kernel
noncomputable def frame806 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 19, changes := [(264, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832812, preBeta := 5439691, preBonus := 5834143, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337937, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337944, updateProofs := some (191021, 376782), numericProof := 75846, slack := 0}
noncomputable def case806 : PhysicalCase := ⟨1,262,.east,.push 263 (.stay 264),frame806⟩
theorem frame806_checked : CountedLocalCaseData.check data frame806 = true := by decide +kernel
theorem case806_fitted : fits case806 = true := by decide +kernel
noncomputable def frame807 : CountedLocalCase.Frame := {bindings := [(262, false), (263, true), (264, false)], budget := 19, changes := [(262, true), (263, false)], beforeBeta := 5439691, beforeBonus := 5832815, afterBeta := 5439691, afterBonus := 5832812, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337958, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (192504, 376803), numericProof := 75847, slack := 2}
noncomputable def case807 : PhysicalCase := ⟨1,264,.west,.push 263 (.stay 262),frame807⟩
theorem frame807_checked : CountedLocalCaseData.check data frame807 = true := by decide +kernel
theorem case807_fitted : fits case807 = true := by decide +kernel
noncomputable def frame808 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 19, changes := [(238, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832815, preBeta := 5439691, preBonus := 5834146, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337979, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337998, updateProofs := some (194360, 376824), numericProof := 75865, slack := 0}
noncomputable def case808 : PhysicalCase := ⟨1,290,.north,.push 264 (.stay 238),frame808⟩
theorem frame808_checked : CountedLocalCaseData.check data frame808 = true := by decide +kernel
theorem case808_fitted : fits case808 = true := by decide +kernel
noncomputable def frame809 : CountedLocalCase.Frame := {bindings := [(238, false), (264, true), (290, false)], budget := 19, changes := [(290, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832818, afterBeta := 5439691, afterBonus := 5832815, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338011, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (196259, 376845), numericProof := 75866, slack := 4}
noncomputable def case809 : PhysicalCase := ⟨1,238,.south,.push 264 (.stay 290),frame809⟩
theorem frame809_checked : CountedLocalCaseData.check data frame809 = true := by decide +kernel
theorem case809_fitted : fits case809 = true := by decide +kernel
noncomputable def frame810 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 19, changes := [(265, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832812, afterBeta := 5439691, afterBonus := 5832815, preBeta := 5439691, preBonus := 5834150, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338032, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338053, updateProofs := some (198116, 376866), numericProof := 75867, slack := 2}
noncomputable def case810 : PhysicalCase := ⟨1,263,.east,.push 264 (.stay 265),frame810⟩
theorem frame810_checked : CountedLocalCaseData.check data frame810 = true := by decide +kernel
theorem case810_fitted : fits case810 = true := by decide +kernel
noncomputable def frame811 : CountedLocalCase.Frame := {bindings := [(263, false), (264, true), (265, false)], budget := 19, changes := [(263, true), (264, false)], beforeBeta := 5439691, beforeBonus := 5832816, afterBeta := 5439691, afterBonus := 5832815, preBeta := 5439691, preBonus := 5834153, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338074, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338081, updateProofs := some (199972, 376887), numericProof := 75868, slack := 2}
noncomputable def case811 : PhysicalCase := ⟨1,265,.west,.push 264 (.stay 263),frame811⟩
theorem frame811_checked : CountedLocalCaseData.check data frame811 = true := by decide +kernel
theorem case811_fitted : fits case811 = true := by decide +kernel
noncomputable def frame812 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 19, changes := [(239, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832817, afterBeta := 5439691, afterBonus := 5832816, preBeta := 5439691, preBonus := 5834156, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338102, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338123, updateProofs := some (201896, 376908), numericProof := 75869, slack := 0}
noncomputable def case812 : PhysicalCase := ⟨1,291,.north,.push 265 (.stay 239),frame812⟩
theorem frame812_checked : CountedLocalCaseData.check data frame812 = true := by decide +kernel
theorem case812_fitted : fits case812 = true := by decide +kernel
noncomputable def frame813 : CountedLocalCase.Frame := {bindings := [(239, false), (265, true), (291, false)], budget := 19, changes := [(291, true), (265, false)], beforeBeta := 5439691, beforeBonus := 5832784, afterBeta := 5439691, afterBonus := 5832816, preBeta := 5439691, preBonus := 5834158, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338137, restrictionAfterBeta := 8531, restrictionAfterBonus := 1338139, updateProofs := some (203881, 376929), numericProof := 75870, slack := 2}
noncomputable def case813 : PhysicalCase := ⟨1,239,.south,.push 265 (.stay 291),frame813⟩
theorem frame813_checked : CountedLocalCaseData.check data frame813 = true := by decide +kernel
theorem case813_fitted : fits case813 = true := by decide +kernel
noncomputable def frame814 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 19, changes := [(244, true), (270, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338141, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (208395, 376931), numericProof := 75871, slack := 0}
noncomputable def case814 : PhysicalCase := ⟨1,296,.north,.push 270 (.stay 244),frame814⟩
theorem frame814_checked : CountedLocalCaseData.check data frame814 = true := by decide +kernel
theorem case814_fitted : fits case814 = true := by decide +kernel
noncomputable def frame815 : CountedLocalCase.Frame := {bindings := [(244, false), (270, true), (296, false)], budget := 19, changes := [(296, true), (270, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338141, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (213190, 376933), numericProof := 75872, slack := 1}
noncomputable def case815 : PhysicalCase := ⟨1,244,.south,.push 270 (.stay 296),frame815⟩
theorem frame815_checked : CountedLocalCaseData.check data frame815 = true := by decide +kernel
theorem case815_fitted : fits case815 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
