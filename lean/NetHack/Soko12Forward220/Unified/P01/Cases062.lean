import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame744 : CountedLocalCase.Frame := {bindings := [(191, false), (192, true), (193, false)], budget := 19, changes := [(193, true), (192, false)], beforeBeta := 5439691, beforeBonus := 5832788, afterBeta := 5439699, afterBonus := 5832791, preBeta := 5439972, preBonus := 5834035, restrictionBeforeBeta := 972596, restrictionBeforeBonus := 1337179, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337181, updateProofs := some (52122, 376219), numericProof := 75701, slack := 2}
noncomputable def case744 : PhysicalCase := ⟨1,191,.east,.push 192 (.stay 193),frame744⟩
theorem frame744_checked : CountedLocalCaseData.check data frame744 = true := by decide +kernel
theorem case744_fitted : fits case744 = true := by decide +kernel
noncomputable def frame745 : CountedLocalCase.Frame := {bindings := [(191, false), (192, true), (193, false)], budget := 19, changes := [(191, true), (192, false)], beforeBeta := 5439700, beforeBonus := 5832797, afterBeta := 5439699, afterBonus := 5832791, preBeta := 5439972, preBonus := 5834037, restrictionBeforeBeta := 975681, restrictionBeforeBonus := 1337183, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337185, updateProofs := some (54133, 376221), numericProof := 75705, slack := 0}
noncomputable def case745 : PhysicalCase := ⟨1,193,.west,.push 192 (.stay 191),frame745⟩
theorem frame745_checked : CountedLocalCaseData.check data frame745 = true := by decide +kernel
theorem case745_fitted : fits case745 = true := by decide +kernel
noncomputable def frame746 : CountedLocalCase.Frame := {bindings := [(167, false), (193, true), (219, false)], budget := 19, changes := [(167, true), (193, false)], beforeBeta := 5439691, beforeBonus := 5832799, afterBeta := 5439700, afterBonus := 5832797, preBeta := 5439972, preBonus := 5834040, restrictionBeforeBeta := 978580, restrictionBeforeBonus := 1337187, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337189, updateProofs := some (55622, 376223), numericProof := 75709, slack := 2}
noncomputable def case746 : PhysicalCase := ⟨1,219,.north,.push 193 (.stay 167),frame746⟩
theorem frame746_checked : CountedLocalCaseData.check data frame746 = true := by decide +kernel
theorem case746_fitted : fits case746 = true := by decide +kernel
noncomputable def frame747 : CountedLocalCase.Frame := {bindings := [(167, false), (193, true), (219, false)], budget := 19, changes := [(219, true), (193, false)], beforeBeta := 5439691, beforeBonus := 5832798, afterBeta := 5439700, afterBonus := 5832797, preBeta := 5439972, preBonus := 5834043, restrictionBeforeBeta := 978580, restrictionBeforeBonus := 1337191, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337193, updateProofs := some (59581, 376225), numericProof := 75711, slack := 2}
noncomputable def case747 : PhysicalCase := ⟨1,167,.south,.push 193 (.stay 219),frame747⟩
theorem frame747_checked : CountedLocalCaseData.check data frame747 = true := by decide +kernel
theorem case747_fitted : fits case747 = true := by decide +kernel
noncomputable def frame748 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 19, changes := [(194, true), (193, false)], beforeBeta := 5439699, beforeBonus := 5832791, afterBeta := 5439700, afterBonus := 5832797, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 1337195, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (61968, 376227), numericProof := 75712, slack := 3}
noncomputable def case748 : PhysicalCase := ⟨1,192,.east,.push 193 (.stay 194),frame748⟩
theorem frame748_checked : CountedLocalCaseData.check data frame748 = true := by decide +kernel
theorem case748_fitted : fits case748 = true := by decide +kernel
noncomputable def frame749 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 19, changes := [(192, true), (193, false)], beforeBeta := 5439691, beforeBonus := 5832804, afterBeta := 5439700, afterBonus := 5832797, preBeta := 5439972, preBonus := 5834047, restrictionBeforeBeta := 986470, restrictionBeforeBonus := 1337197, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337199, updateProofs := some (64129, 376229), numericProof := 75716, slack := 0}
noncomputable def case749 : PhysicalCase := ⟨1,194,.west,.push 193 (.stay 192),frame749⟩
theorem frame749_checked : CountedLocalCaseData.check data frame749 = true := by decide +kernel
theorem case749_fitted : fits case749 = true := by decide +kernel
noncomputable def frame750 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 19, changes := [(168, true), (194, false)], beforeBeta := 5439691, beforeBonus := 5832804, afterBeta := 5439691, afterBonus := 5832804, preBeta := 5440874, preBonus := 5834050, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 1337201, restrictionAfterBeta := 937363, restrictionAfterBonus := 1337203, updateProofs := some (66065, 376231), numericProof := 75720, slack := 1}
noncomputable def case750 : PhysicalCase := ⟨1,220,.north,.push 194 (.stay 168),frame750⟩
theorem frame750_checked : CountedLocalCaseData.check data frame750 = true := by decide +kernel
theorem case750_fitted : fits case750 = true := by decide +kernel
noncomputable def frame751 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 19, changes := [(220, true), (194, false)], beforeBeta := 5439696, beforeBonus := 5832805, afterBeta := 5439691, afterBonus := 5832804, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 1337205, restrictionAfterBeta := 14070, restrictionAfterBonus := 3, updateProofs := some (70632, 376233), numericProof := 75721, slack := 1}
noncomputable def case751 : PhysicalCase := ⟨1,168,.south,.push 194 (.stay 220),frame751⟩
theorem frame751_checked : CountedLocalCaseData.check data frame751 = true := by decide +kernel
theorem case751_fitted : fits case751 = true := by decide +kernel
noncomputable def frame752 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 19, changes := [(184, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832796, preBeta := 5439691, preBonus := 5834052, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337226, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337240, updateProofs := some (71708, 376254), numericProof := 75732, slack := 0}
noncomputable def case752 : PhysicalCase := ⟨1,236,.north,.push 210 (.stay 184),frame752⟩
theorem frame752_checked : CountedLocalCaseData.check data frame752 = true := by decide +kernel
theorem case752_fitted : fits case752 = true := by decide +kernel
noncomputable def frame753 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 19, changes := [(236, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832795, afterBeta := 5439691, afterBonus := 5832796, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337259, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (72918, 376275), numericProof := 75733, slack := 2}
noncomputable def case753 : PhysicalCase := ⟨1,184,.south,.push 210 (.stay 236),frame753⟩
theorem frame753_checked : CountedLocalCaseData.check data frame753 = true := by decide +kernel
theorem case753_fitted : fits case753 = true := by decide +kernel
noncomputable def frame754 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 19, changes := [(185, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832813, afterBeta := 5439691, afterBonus := 5832794, preBeta := 5439691, preBonus := 5834056, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337280, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337287, updateProofs := some (73977, 376296), numericProof := 75734, slack := 0}
noncomputable def case754 : PhysicalCase := ⟨1,237,.north,.push 211 (.stay 185),frame754⟩
theorem frame754_checked : CountedLocalCaseData.check data frame754 = true := by decide +kernel
theorem case754_fitted : fits case754 = true := by decide +kernel
noncomputable def frame755 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 19, changes := [(237, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832790, afterBeta := 5439691, afterBonus := 5832794, preBeta := 5439691, preBonus := 5834058, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337301, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337308, updateProofs := some (75362, 376317), numericProof := 75735, slack := 2}
noncomputable def case755 : PhysicalCase := ⟨1,185,.south,.push 211 (.stay 237),frame755⟩
theorem frame755_checked : CountedLocalCaseData.check data frame755 = true := by decide +kernel
theorem case755_fitted : fits case755 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
