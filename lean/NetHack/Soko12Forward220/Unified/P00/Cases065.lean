import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame780 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 20, changes := [(210, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 5833498, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1078317, restrictionAfterBeta := 8531, restrictionAfterBonus := 1078878, updateProofs := some (138557, 138483), numericProof := 56749, slack := 0}
noncomputable def case780 : PhysicalCase := ⟨0,262,.north,.push 236 (.stay 210),frame780⟩
theorem frame780_checked : CountedLocalCaseData.check data frame780 = true := by decide +kernel
theorem case780_fitted : fits case780 = true := by decide +kernel
noncomputable def frame781 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 20, changes := [(262, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832766, afterBeta := 5439691, afterBonus := 5832750, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1079274, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (140071, 139997), numericProof := 56750, slack := 2}
noncomputable def case781 : PhysicalCase := ⟨0,210,.south,.push 236 (.stay 262),frame781⟩
theorem frame781_checked : CountedLocalCaseData.check data frame781 = true := by decide +kernel
theorem case781_fitted : fits case781 = true := by decide +kernel
noncomputable def frame782 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 20, changes := [(211, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832764, afterBeta := 5439691, afterBonus := 5832767, preBeta := 5439691, preBonus := 5833500, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1080636, restrictionAfterBeta := 8531, restrictionAfterBonus := 1081418, updateProofs := some (141440, 141366), numericProof := 56751, slack := 0}
noncomputable def case782 : PhysicalCase := ⟨0,263,.north,.push 237 (.stay 211),frame782⟩
theorem frame782_checked : CountedLocalCaseData.check data frame782 = true := by decide +kernel
theorem case782_fitted : fits case782 = true := by decide +kernel
noncomputable def frame783 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 20, changes := [(263, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832768, afterBeta := 5439691, afterBonus := 5832767, preBeta := 5439691, preBonus := 5833502, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1082286, restrictionAfterBeta := 8531, restrictionAfterBonus := 1082665, updateProofs := some (142896, 142822), numericProof := 56752, slack := 2}
noncomputable def case783 : PhysicalCase := ⟨0,211,.south,.push 237 (.stay 263),frame783⟩
theorem frame783_checked : CountedLocalCaseData.check data frame783 = true := by decide +kernel
theorem case783_fitted : fits case783 = true := by decide +kernel
noncomputable def frame784 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 20, changes := [(238, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832767, preBeta := 5439691, preBonus := 5833505, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1084029, restrictionAfterBeta := 8531, restrictionAfterBonus := 1085259, updateProofs := some (144294, 144220), numericProof := 57176, slack := 0}
noncomputable def case784 : PhysicalCase := ⟨0,236,.east,.push 237 (.stay 238),frame784⟩
theorem frame784_checked : CountedLocalCaseData.check data frame784 = true := by decide +kernel
theorem case784_fitted : fits case784 = true := by decide +kernel
noncomputable def frame785 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 20, changes := [(236, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832758, afterBeta := 5439691, afterBonus := 5832767, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1085821, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (145671, 145597), numericProof := 57177, slack := 2}
noncomputable def case785 : PhysicalCase := ⟨0,238,.west,.push 237 (.stay 236),frame785⟩
theorem frame785_checked : CountedLocalCaseData.check data frame785 = true := by decide +kernel
theorem case785_fitted : fits case785 = true := by decide +kernel
noncomputable def frame786 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 20, changes := [(212, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832749, afterBeta := 5439691, afterBonus := 5832758, preBeta := 5439691, preBonus := 5833509, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1087245, restrictionAfterBeta := 8531, restrictionAfterBonus := 1087760, updateProofs := some (146345, 146271), numericProof := 57178, slack := 0}
noncomputable def case786 : PhysicalCase := ⟨0,264,.north,.push 238 (.stay 212),frame786⟩
theorem frame786_checked : CountedLocalCaseData.check data frame786 = true := by decide +kernel
theorem case786_fitted : fits case786 = true := by decide +kernel
noncomputable def frame787 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 20, changes := [(264, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832744, afterBeta := 5439691, afterBonus := 5832758, preBeta := 5439691, preBonus := 5833511, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1088788, restrictionAfterBeta := 8531, restrictionAfterBonus := 1089025, updateProofs := some (147122, 147048), numericProof := 57179, slack := 2}
noncomputable def case787 : PhysicalCase := ⟨0,212,.south,.push 238 (.stay 264),frame787⟩
theorem frame787_checked : CountedLocalCaseData.check data frame787 = true := by decide +kernel
theorem case787_fitted : fits case787 = true := by decide +kernel
noncomputable def frame788 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 20, changes := [(239, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832767, afterBeta := 5439691, afterBonus := 5832758, preBeta := 5439691, preBonus := 5833514, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1090347, restrictionAfterBeta := 8531, restrictionAfterBonus := 1090942, updateProofs := some (147813, 147739), numericProof := 57180, slack := 2}
noncomputable def case788 : PhysicalCase := ⟨0,237,.east,.push 238 (.stay 239),frame788⟩
theorem frame788_checked : CountedLocalCaseData.check data frame788 = true := by decide +kernel
theorem case788_fitted : fits case788 = true := by decide +kernel
noncomputable def frame789 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 20, changes := [(237, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832740, afterBeta := 5439691, afterBonus := 5832758, preBeta := 5439691, preBonus := 5833517, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1092998, restrictionAfterBeta := 8531, restrictionAfterBonus := 1093474, updateProofs := some (148494, 148420), numericProof := 57181, slack := 2}
noncomputable def case789 : PhysicalCase := ⟨0,239,.west,.push 238 (.stay 237),frame789⟩
theorem frame789_checked : CountedLocalCaseData.check data frame789 = true := by decide +kernel
theorem case789_fitted : fits case789 = true := by decide +kernel
noncomputable def frame790 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 20, changes := [(213, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832746, afterBeta := 5439691, afterBonus := 5832740, preBeta := 5439691, preBonus := 5833519, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1095015, restrictionAfterBeta := 8531, restrictionAfterBonus := 1095746, updateProofs := some (150523, 150449), numericProof := 57208, slack := 0}
noncomputable def case790 : PhysicalCase := ⟨0,265,.north,.push 239 (.stay 213),frame790⟩
theorem frame790_checked : CountedLocalCaseData.check data frame790 = true := by decide +kernel
theorem case790_fitted : fits case790 = true := by decide +kernel
noncomputable def frame791 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 20, changes := [(265, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832738, afterBeta := 5439691, afterBonus := 5832740, preBeta := 5439691, preBonus := 5833522, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1097212, restrictionAfterBeta := 8531, restrictionAfterBonus := 1098706, updateProofs := some (152932, 152858), numericProof := 57209, slack := 2}
noncomputable def case791 : PhysicalCase := ⟨0,213,.south,.push 239 (.stay 265),frame791⟩
theorem frame791_checked : CountedLocalCaseData.check data frame791 = true := by decide +kernel
theorem case791_fitted : fits case791 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
