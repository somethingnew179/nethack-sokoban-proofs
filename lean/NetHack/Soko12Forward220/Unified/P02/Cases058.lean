import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame696 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 18, changes := [(143, true), (142, false)], beforeBeta := 5439692, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 949, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2806, 2718), numericProof := 76315, slack := 1}
noncomputable def case696 : PhysicalCase := ⟨2,141,.east,.push 142 (.stay 143),frame696⟩
theorem frame696_checked : CountedLocalCaseData.check data frame696 = true := by decide +kernel
theorem case696_fitted : fits case696 = true := by decide +kernel
noncomputable def frame697 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 18, changes := [(141, true), (142, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2883, 2807), numericProof := 76315, slack := 1}
noncomputable def case697 : PhysicalCase := ⟨2,143,.west,.push 142 (.stay 141),frame697⟩
theorem frame697_checked : CountedLocalCaseData.check data frame697 = true := by decide +kernel
theorem case697_fitted : fits case697 = true := by decide +kernel
noncomputable def frame698 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 18, changes := [(117, true), (143, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2936, 2884), numericProof := 76316, slack := 1}
noncomputable def case698 : PhysicalCase := ⟨2,169,.north,.push 143 (.stay 117),frame698⟩
theorem frame698_checked : CountedLocalCaseData.check data frame698 = true := by decide +kernel
theorem case698_fitted : fits case698 = true := by decide +kernel
noncomputable def frame699 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 18, changes := [(169, true), (143, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (3540, 2937), numericProof := 76316, slack := 1}
noncomputable def case699 : PhysicalCase := ⟨2,117,.south,.push 143 (.stay 169),frame699⟩
theorem frame699_checked : CountedLocalCaseData.check data frame699 = true := by decide +kernel
theorem case699_fitted : fits case699 = true := by decide +kernel
noncomputable def frame700 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 18, changes := [(132, true), (158, false)], beforeBeta := 5439691, beforeBonus := 5832840, afterBeta := 5439693, afterBonus := 5832841, preBeta := 5440582, preBonus := 5834378, restrictionBeforeBeta := 926660, restrictionBeforeBonus := 1340757, restrictionAfterBeta := 926964, restrictionAfterBonus := 1340761, updateProofs := some (3812, 377603), numericProof := 76321, slack := 0}
noncomputable def case700 : PhysicalCase := ⟨2,184,.north,.push 158 (.stay 132),frame700⟩
theorem frame700_checked : CountedLocalCaseData.check data frame700 = true := by decide +kernel
theorem case700_fitted : fits case700 = true := by decide +kernel
noncomputable def frame701 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 18, changes := [(184, true), (158, false)], beforeBeta := 5439688, beforeBonus := 5832834, afterBeta := 5439693, afterBonus := 5832841, preBeta := 5439745, preBonus := 5834381, restrictionBeforeBeta := 927173, restrictionBeforeBonus := 1340765, restrictionAfterBeta := 927484, restrictionAfterBonus := 1340769, updateProofs := some (4487, 377610), numericProof := 76326, slack := 2}
noncomputable def case701 : PhysicalCase := ⟨2,132,.south,.push 158 (.stay 184),frame701⟩
theorem frame701_checked : CountedLocalCaseData.check data frame701 = true := by decide +kernel
theorem case701_fitted : fits case701 = true := by decide +kernel
noncomputable def frame702 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 18, changes := [(159, true), (158, false)], beforeBeta := 5439686, beforeBonus := 5832835, afterBeta := 5439693, afterBonus := 5832841, preBeta := 5440722, preBonus := 5834384, restrictionBeforeBeta := 927579, restrictionBeforeBonus := 1340776, restrictionAfterBeta := 927921, restrictionAfterBonus := 1340780, updateProofs := some (4902, 377617), numericProof := 76331, slack := 0}
noncomputable def case702 : PhysicalCase := ⟨2,157,.east,.push 158 (.stay 159),frame702⟩
theorem frame702_checked : CountedLocalCaseData.check data frame702 = true := by decide +kernel
theorem case702_fitted : fits case702 = true := by decide +kernel
noncomputable def frame703 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 18, changes := [(157, true), (158, false)], beforeBeta := 5439694, beforeBonus := 5832842, afterBeta := 5439693, afterBonus := 5832841, preBeta := 5439745, preBonus := 0, restrictionBeforeBeta := 928140, restrictionBeforeBonus := 1340787, restrictionAfterBeta := 928456, restrictionAfterBonus := 3, updateProofs := some (5209, 377624), numericProof := 76332, slack := 11}
noncomputable def case703 : PhysicalCase := ⟨2,159,.west,.push 158 (.stay 157),frame703⟩
theorem frame703_checked : CountedLocalCaseData.check data frame703 = true := by decide +kernel
theorem case703_fitted : fits case703 = true := by decide +kernel
noncomputable def frame704 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 18, changes := [(133, true), (159, false)], beforeBeta := 5439691, beforeBonus := 5832838, afterBeta := 5439694, afterBonus := 5832842, preBeta := 5440740, preBonus := 5834388, restrictionBeforeBeta := 928483, restrictionBeforeBonus := 1340794, restrictionAfterBeta := 928960, restrictionAfterBonus := 1340801, updateProofs := some (5531, 377631), numericProof := 76387, slack := 0}
noncomputable def case704 : PhysicalCase := ⟨2,185,.north,.push 159 (.stay 133),frame704⟩
theorem frame704_checked : CountedLocalCaseData.check data frame704 = true := by decide +kernel
theorem case704_fitted : fits case704 = true := by decide +kernel
noncomputable def frame705 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 18, changes := [(185, true), (159, false)], beforeBeta := 5439689, beforeBonus := 5832832, afterBeta := 5439694, afterBonus := 5832842, preBeta := 5439893, preBonus := 5834391, restrictionBeforeBeta := 929184, restrictionBeforeBonus := 1340808, restrictionAfterBeta := 929487, restrictionAfterBonus := 1340812, updateProofs := some (6289, 377638), numericProof := 76392, slack := 2}
noncomputable def case705 : PhysicalCase := ⟨2,133,.south,.push 159 (.stay 185),frame705⟩
theorem frame705_checked : CountedLocalCaseData.check data frame705 = true := by decide +kernel
theorem case705_fitted : fits case705 = true := by decide +kernel
noncomputable def frame706 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 18, changes := [(160, true), (159, false)], beforeBeta := 5439693, beforeBonus := 5832841, afterBeta := 5439694, afterBonus := 5832842, preBeta := 5440767, preBonus := 5834394, restrictionBeforeBeta := 929592, restrictionBeforeBonus := 1340819, restrictionAfterBeta := 929970, restrictionAfterBonus := 1340823, updateProofs := some (6753, 377645), numericProof := 76398, slack := 0}
noncomputable def case706 : PhysicalCase := ⟨2,158,.east,.push 159 (.stay 160),frame706⟩
theorem frame706_checked : CountedLocalCaseData.check data frame706 = true := by decide +kernel
theorem case706_fitted : fits case706 = true := by decide +kernel
noncomputable def frame707 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 18, changes := [(158, true), (159, false)], beforeBeta := 5439695, beforeBonus := 5832833, afterBeta := 5439694, afterBonus := 5832842, preBeta := 5440731, preBonus := 5834397, restrictionBeforeBeta := 930173, restrictionBeforeBonus := 1340830, restrictionAfterBeta := 930456, restrictionAfterBonus := 1340837, updateProofs := some (7150, 377652), numericProof := 76421, slack := 2}
noncomputable def case707 : PhysicalCase := ⟨2,160,.west,.push 159 (.stay 158),frame707⟩
theorem frame707_checked : CountedLocalCaseData.check data frame707 = true := by decide +kernel
theorem case707_fitted : fits case707 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
