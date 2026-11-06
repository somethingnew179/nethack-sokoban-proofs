import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame744 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 17, changes := [(192, true), (191, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (42814, 40871), numericProof := 77149, slack := 2}
noncomputable def case744 : PhysicalCase := ⟨3,190,.east,.push 191 (.stay 192),frame744⟩
theorem frame744_checked : CountedLocalCaseData.check data frame744 = true := by decide +kernel
theorem case744_fitted : fits case744 = true := by decide +kernel
noncomputable def frame745 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 17, changes := [(190, true), (191, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (44466, 42815), numericProof := 77150, slack := 0}
noncomputable def case745 : PhysicalCase := ⟨3,192,.west,.push 191 (.stay 190),frame745⟩
theorem frame745_checked : CountedLocalCaseData.check data frame745 = true := by decide +kernel
theorem case745_fitted : fits case745 = true := by decide +kernel
noncomputable def frame746 : CountedLocalCase.Frame := {bindings := [(166, false), (192, true), (218, false)], budget := 17, changes := [(166, true), (192, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439699, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 967905, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (45652, 44467), numericProof := 77151, slack := 2}
noncomputable def case746 : PhysicalCase := ⟨3,218,.north,.push 192 (.stay 166),frame746⟩
theorem frame746_checked : CountedLocalCaseData.check data frame746 = true := by decide +kernel
theorem case746_fitted : fits case746 = true := by decide +kernel
noncomputable def frame747 : CountedLocalCase.Frame := {bindings := [(166, false), (192, true), (218, false)], budget := 17, changes := [(218, true), (192, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439699, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 967905, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (49659, 45653), numericProof := 77151, slack := 2}
noncomputable def case747 : PhysicalCase := ⟨3,166,.south,.push 192 (.stay 218),frame747⟩
theorem frame747_checked : CountedLocalCaseData.check data frame747 = true := by decide +kernel
theorem case747_fitted : fits case747 = true := by decide +kernel
noncomputable def frame748 : CountedLocalCase.Frame := {bindings := [(191, false), (192, true), (193, false)], budget := 17, changes := [(193, true), (192, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439699, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 972596, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (52122, 49660), numericProof := 77152, slack := 2}
noncomputable def case748 : PhysicalCase := ⟨3,191,.east,.push 192 (.stay 193),frame748⟩
theorem frame748_checked : CountedLocalCaseData.check data frame748 = true := by decide +kernel
theorem case748_fitted : fits case748 = true := by decide +kernel
noncomputable def frame749 : CountedLocalCase.Frame := {bindings := [(191, false), (192, true), (193, false)], budget := 17, changes := [(191, true), (192, false)], beforeBeta := 5439700, beforeBonus := 0, afterBeta := 5439699, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 975681, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (54133, 52123), numericProof := 77153, slack := 0}
noncomputable def case749 : PhysicalCase := ⟨3,193,.west,.push 192 (.stay 191),frame749⟩
theorem frame749_checked : CountedLocalCaseData.check data frame749 = true := by decide +kernel
theorem case749_fitted : fits case749 = true := by decide +kernel
noncomputable def frame750 : CountedLocalCase.Frame := {bindings := [(167, false), (193, true), (219, false)], budget := 17, changes := [(167, true), (193, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439700, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 978580, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (55622, 54134), numericProof := 77154, slack := 2}
noncomputable def case750 : PhysicalCase := ⟨3,219,.north,.push 193 (.stay 167),frame750⟩
theorem frame750_checked : CountedLocalCaseData.check data frame750 = true := by decide +kernel
theorem case750_fitted : fits case750 = true := by decide +kernel
noncomputable def frame751 : CountedLocalCase.Frame := {bindings := [(167, false), (193, true), (219, false)], budget := 17, changes := [(219, true), (193, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439700, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 978580, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (59581, 55623), numericProof := 77154, slack := 2}
noncomputable def case751 : PhysicalCase := ⟨3,167,.south,.push 193 (.stay 219),frame751⟩
theorem frame751_checked : CountedLocalCaseData.check data frame751 = true := by decide +kernel
theorem case751_fitted : fits case751 = true := by decide +kernel
noncomputable def frame752 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 17, changes := [(194, true), (193, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439700, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (61968, 59582), numericProof := 77155, slack := 3}
noncomputable def case752 : PhysicalCase := ⟨3,192,.east,.push 193 (.stay 194),frame752⟩
theorem frame752_checked : CountedLocalCaseData.check data frame752 = true := by decide +kernel
theorem case752_fitted : fits case752 = true := by decide +kernel
noncomputable def frame753 : CountedLocalCase.Frame := {bindings := [(192, false), (193, true), (194, false)], budget := 17, changes := [(192, true), (193, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439700, afterBonus := 0, preBeta := 5439972, preBonus := 0, restrictionBeforeBeta := 986470, restrictionBeforeBonus := 3, restrictionAfterBeta := 969324, restrictionAfterBonus := 3, updateProofs := some (64129, 61969), numericProof := 77156, slack := 0}
noncomputable def case753 : PhysicalCase := ⟨3,194,.west,.push 193 (.stay 192),frame753⟩
theorem frame753_checked : CountedLocalCaseData.check data frame753 = true := by decide +kernel
theorem case753_fitted : fits case753 = true := by decide +kernel
noncomputable def frame754 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 17, changes := [(168, true), (194, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440874, preBonus := 0, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 3, restrictionAfterBeta := 937363, restrictionAfterBonus := 3, updateProofs := some (66065, 64130), numericProof := 77157, slack := 1}
noncomputable def case754 : PhysicalCase := ⟨3,220,.north,.push 194 (.stay 168),frame754⟩
theorem frame754_checked : CountedLocalCaseData.check data frame754 = true := by decide +kernel
theorem case754_fitted : fits case754 = true := by decide +kernel
noncomputable def frame755 : CountedLocalCase.Frame := {bindings := [(168, false), (194, true), (220, false)], budget := 17, changes := [(220, true), (194, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 14070, restrictionAfterBonus := 3, updateProofs := some (70632, 66066), numericProof := 77158, slack := 1}
noncomputable def case755 : PhysicalCase := ⟨3,168,.south,.push 194 (.stay 220),frame755⟩
theorem frame755_checked : CountedLocalCaseData.check data frame755 = true := by decide +kernel
theorem case755_fitted : fits case755 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
