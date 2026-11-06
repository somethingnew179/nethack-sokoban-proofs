import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame696 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 16, changes := [(142, true), (141, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2265, 2116), numericProof := 77624, slack := 1}
noncomputable def case696 : PhysicalCase := ⟨4,140,.east,.push 141 (.stay 142),frame696⟩
theorem frame696_checked : CountedLocalCaseData.check data frame696 = true := by decide +kernel
theorem case696_fitted : fits case696 = true := by decide +kernel
noncomputable def frame697 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 16, changes := [(140, true), (141, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2377, 2266), numericProof := 77625, slack := 1}
noncomputable def case697 : PhysicalCase := ⟨4,142,.west,.push 141 (.stay 140),frame697⟩
theorem frame697_checked : CountedLocalCaseData.check data frame697 = true := by decide +kernel
theorem case697_fitted : fits case697 = true := by decide +kernel
noncomputable def frame698 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 16, changes := [(116, true), (142, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2430, 2378), numericProof := 77626, slack := 1}
noncomputable def case698 : PhysicalCase := ⟨4,168,.north,.push 142 (.stay 116),frame698⟩
theorem frame698_checked : CountedLocalCaseData.check data frame698 = true := by decide +kernel
theorem case698_fitted : fits case698 = true := by decide +kernel
noncomputable def frame699 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 16, changes := [(168, true), (142, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2717, 2431), numericProof := 77626, slack := 1}
noncomputable def case699 : PhysicalCase := ⟨4,116,.south,.push 142 (.stay 168),frame699⟩
theorem frame699_checked : CountedLocalCaseData.check data frame699 = true := by decide +kernel
theorem case699_fitted : fits case699 = true := by decide +kernel
noncomputable def frame700 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 16, changes := [(143, true), (142, false)], beforeBeta := 5439692, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 949, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2806, 2718), numericProof := 77627, slack := 1}
noncomputable def case700 : PhysicalCase := ⟨4,141,.east,.push 142 (.stay 143),frame700⟩
theorem frame700_checked : CountedLocalCaseData.check data frame700 = true := by decide +kernel
theorem case700_fitted : fits case700 = true := by decide +kernel
noncomputable def frame701 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 16, changes := [(141, true), (142, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2883, 2807), numericProof := 77627, slack := 1}
noncomputable def case701 : PhysicalCase := ⟨4,143,.west,.push 142 (.stay 141),frame701⟩
theorem frame701_checked : CountedLocalCaseData.check data frame701 = true := by decide +kernel
theorem case701_fitted : fits case701 = true := by decide +kernel
noncomputable def frame702 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 16, changes := [(117, true), (143, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2936, 2884), numericProof := 77628, slack := 1}
noncomputable def case702 : PhysicalCase := ⟨4,169,.north,.push 143 (.stay 117),frame702⟩
theorem frame702_checked : CountedLocalCaseData.check data frame702 = true := by decide +kernel
theorem case702_fitted : fits case702 = true := by decide +kernel
noncomputable def frame703 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 16, changes := [(169, true), (143, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (3540, 2937), numericProof := 77628, slack := 1}
noncomputable def case703 : PhysicalCase := ⟨4,117,.south,.push 143 (.stay 169),frame703⟩
theorem frame703_checked : CountedLocalCaseData.check data frame703 = true := by decide +kernel
theorem case703_fitted : fits case703 = true := by decide +kernel
noncomputable def frame704 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 16, changes := [(132, true), (158, false)], beforeBeta := 5439691, beforeBonus := 5832896, afterBeta := 5439693, afterBonus := 5832892, preBeta := 5440582, preBonus := 5834989, restrictionBeforeBeta := 926660, restrictionBeforeBonus := 1344214, restrictionAfterBeta := 926964, restrictionAfterBonus := 1344216, updateProofs := some (3812, 378655), numericProof := 77629, slack := 0}
noncomputable def case704 : PhysicalCase := ⟨4,184,.north,.push 158 (.stay 132),frame704⟩
theorem frame704_checked : CountedLocalCaseData.check data frame704 = true := by decide +kernel
theorem case704_fitted : fits case704 = true := by decide +kernel
noncomputable def frame705 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 16, changes := [(184, true), (158, false)], beforeBeta := 5439688, beforeBonus := 5832890, afterBeta := 5439693, afterBonus := 5832892, preBeta := 5439745, preBonus := 5835001, restrictionBeforeBeta := 927173, restrictionBeforeBonus := 1344218, restrictionAfterBeta := 927484, restrictionAfterBonus := 1344220, updateProofs := some (4487, 378658), numericProof := 77630, slack := 2}
noncomputable def case705 : PhysicalCase := ⟨4,132,.south,.push 158 (.stay 184),frame705⟩
theorem frame705_checked : CountedLocalCaseData.check data frame705 = true := by decide +kernel
theorem case705_fitted : fits case705 = true := by decide +kernel
noncomputable def frame706 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 16, changes := [(159, true), (158, false)], beforeBeta := 5439686, beforeBonus := 5832891, afterBeta := 5439693, afterBonus := 5832892, preBeta := 5440722, preBonus := 5835002, restrictionBeforeBeta := 927579, restrictionBeforeBonus := 1344223, restrictionAfterBeta := 927921, restrictionAfterBonus := 1344225, updateProofs := some (4902, 378661), numericProof := 77631, slack := 0}
noncomputable def case706 : PhysicalCase := ⟨4,157,.east,.push 158 (.stay 159),frame706⟩
theorem frame706_checked : CountedLocalCaseData.check data frame706 = true := by decide +kernel
theorem case706_fitted : fits case706 = true := by decide +kernel
noncomputable def frame707 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 16, changes := [(157, true), (158, false)], beforeBeta := 5439694, beforeBonus := 5832889, afterBeta := 5439693, afterBonus := 5832892, preBeta := 5439745, preBonus := 0, restrictionBeforeBeta := 928140, restrictionBeforeBonus := 1344228, restrictionAfterBeta := 928456, restrictionAfterBonus := 3, updateProofs := some (5209, 378664), numericProof := 77632, slack := 11}
noncomputable def case707 : PhysicalCase := ⟨4,159,.west,.push 158 (.stay 157),frame707⟩
theorem frame707_checked : CountedLocalCaseData.check data frame707 = true := by decide +kernel
theorem case707_fitted : fits case707 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
