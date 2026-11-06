import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame744 : CountedLocalCase.Frame := {bindings := [(167, false), (193, true), (219, false)], budget := 20, changes := [(167, true), (193, false)], beforeBeta := 5439691, beforeBonus := 5832717, afterBeta := 5439700, afterBonus := 5832719, preBeta := 5439972, preBonus := 5833412, restrictionBeforeBeta := 978580, restrictionBeforeBonus := 980617, restrictionAfterBeta := 969324, restrictionAfterBonus := 981616, updateProofs := some (55622, 55537), numericProof := 40075, slack := 2}
noncomputable def case744 : PhysicalCase := ⟨0,219,.north,.push 193 (.stay 167),frame744⟩
theorem frame744_checked : CountedLocalCaseData.check data frame744 = true := by decide +kernel
theorem case744_fitted : fits case744 = true := by decide +kernel
noncomputable def frame745 : CountedLocalCase.Frame := {bindings := [(167, false), (193, true), (219, false)], budget := 20, changes := [(219, true), (193, false)], beforeBeta := 5439691, beforeBonus := 5832726, afterBeta := 5439700, afterBonus := 5832719, preBeta := 5439972, preBonus := 5833415, restrictionBeforeBeta := 978580, restrictionBeforeBonus := 983278, restrictionAfterBeta := 969324, restrictionAfterBonus := 983786, updateProofs := some (59581, 59496), numericProof := 41895, slack := 2}
noncomputable def case745 : PhysicalCase := ⟨0,167,.south,.push 193 (.stay 219),frame745⟩
theorem frame745_checked : CountedLocalCaseData.check data frame745 = true := by decide +kernel
theorem case745_fitted : fits case745 = true := by decide +kernel
noncomputable def frame746 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 20, changes := [(194, true), (193, false)], beforeBeta := 5439699, beforeBonus := 5832721, afterBeta := 5439700, afterBonus := 5832719, preBeta := 5439972, preBonus := 5833418, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 986102, restrictionAfterBeta := 969324, restrictionAfterBonus := 986405, updateProofs := some (61968, 61883), numericProof := 41896, slack := 3}
noncomputable def case746 : PhysicalCase := ⟨0,192,.east,.push 193 (.stay 194),frame746⟩
theorem frame746_checked : CountedLocalCaseData.check data frame746 = true := by decide +kernel
theorem case746_fitted : fits case746 = true := by decide +kernel
noncomputable def frame747 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 20, changes := [(192, true), (193, false)], beforeBeta := 5439691, beforeBonus := 5832720, afterBeta := 5439700, afterBonus := 5832719, preBeta := 5439972, preBonus := 5833421, restrictionBeforeBeta := 986470, restrictionBeforeBonus := 988215, restrictionAfterBeta := 969324, restrictionAfterBonus := 989525, updateProofs := some (64129, 64048), numericProof := 43556, slack := 0}
noncomputable def case747 : PhysicalCase := ⟨0,194,.west,.push 193 (.stay 192),frame747⟩
theorem frame747_checked : CountedLocalCaseData.check data frame747 = true := by decide +kernel
theorem case747_fitted : fits case747 = true := by decide +kernel
noncomputable def frame748 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 20, changes := [(168, true), (194, false)], beforeBeta := 5439691, beforeBonus := 5832718, afterBeta := 5439691, afterBonus := 5832720, preBeta := 5440874, preBonus := 5833424, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 991472, restrictionAfterBeta := 937363, restrictionAfterBonus := 992623, updateProofs := some (66065, 65991), numericProof := 44279, slack := 1}
noncomputable def case748 : PhysicalCase := ⟨0,220,.north,.push 194 (.stay 168),frame748⟩
theorem frame748_checked : CountedLocalCaseData.check data frame748 = true := by decide +kernel
theorem case748_fitted : fits case748 = true := by decide +kernel
noncomputable def frame749 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 20, changes := [(220, true), (194, false)], beforeBeta := 5439696, beforeBonus := 5832722, afterBeta := 5439691, afterBonus := 5832720, preBeta := 5439691, preBonus := 5833427, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 993314, restrictionAfterBeta := 14070, restrictionAfterBonus := 993395, updateProofs := some (70632, 70558), numericProof := 44280, slack := 1}
noncomputable def case749 : PhysicalCase := ⟨0,168,.south,.push 194 (.stay 220),frame749⟩
theorem frame749_checked : CountedLocalCaseData.check data frame749 = true := by decide +kernel
theorem case749_fitted : fits case749 = true := by decide +kernel
noncomputable def frame750 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 20, changes := [(184, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832750, afterBeta := 5439691, afterBonus := 5832766, preBeta := 5439691, preBonus := 5833430, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 994287, restrictionAfterBeta := 8531, restrictionAfterBonus := 995031, updateProofs := some (71708, 71634), numericProof := 44612, slack := 0}
noncomputable def case750 : PhysicalCase := ⟨0,236,.north,.push 210 (.stay 184),frame750⟩
theorem frame750_checked : CountedLocalCaseData.check data frame750 = true := by decide +kernel
theorem case750_fitted : fits case750 = true := by decide +kernel
noncomputable def frame751 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 20, changes := [(236, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832757, afterBeta := 5439691, afterBonus := 5832766, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 995996, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (72918, 72844), numericProof := 44613, slack := 2}
noncomputable def case751 : PhysicalCase := ⟨0,184,.south,.push 210 (.stay 236),frame751⟩
theorem frame751_checked : CountedLocalCaseData.check data frame751 = true := by decide +kernel
theorem case751_fitted : fits case751 = true := by decide +kernel
noncomputable def frame752 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 20, changes := [(185, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832767, afterBeta := 5439691, afterBonus := 5832768, preBeta := 5439691, preBonus := 5833434, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 997107, restrictionAfterBeta := 8531, restrictionAfterBonus := 997812, updateProofs := some (73977, 73903), numericProof := 44704, slack := 0}
noncomputable def case752 : PhysicalCase := ⟨0,237,.north,.push 211 (.stay 185),frame752⟩
theorem frame752_checked : CountedLocalCaseData.check data frame752 = true := by decide +kernel
theorem case752_fitted : fits case752 = true := by decide +kernel
noncomputable def frame753 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 20, changes := [(237, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832748, afterBeta := 5439691, afterBonus := 5832768, preBeta := 5439691, preBonus := 5833437, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 999222, restrictionAfterBeta := 8531, restrictionAfterBonus := 999720, updateProofs := some (75362, 75288), numericProof := 44705, slack := 2}
noncomputable def case753 : PhysicalCase := ⟨0,185,.south,.push 211 (.stay 237),frame753⟩
theorem frame753_checked : CountedLocalCaseData.check data frame753 = true := by decide +kernel
theorem case753_fitted : fits case753 = true := by decide +kernel
noncomputable def frame754 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 20, changes := [(212, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832766, afterBeta := 5439691, afterBonus := 5832768, preBeta := 5439691, preBonus := 5833440, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1000721, restrictionAfterBeta := 8531, restrictionAfterBonus := 1001785, updateProofs := some (76625, 76551), numericProof := 45116, slack := 0}
noncomputable def case754 : PhysicalCase := ⟨0,210,.east,.push 211 (.stay 212),frame754⟩
theorem frame754_checked : CountedLocalCaseData.check data frame754 = true := by decide +kernel
theorem case754_fitted : fits case754 = true := by decide +kernel
noncomputable def frame755 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 20, changes := [(210, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832744, afterBeta := 5439691, afterBonus := 5832768, preBeta := 5439691, preBonus := 5833443, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1002687, restrictionAfterBeta := 8531, restrictionAfterBonus := 1003079, updateProofs := some (77839, 77765), numericProof := 45117, slack := 2}
noncomputable def case755 : PhysicalCase := ⟨0,212,.west,.push 211 (.stay 210),frame755⟩
theorem frame755_checked : CountedLocalCaseData.check data frame755 = true := by decide +kernel
theorem case755_fitted : fits case755 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
