import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame696 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 19, changes := [(117, true), (143, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439687, afterBonus := 5832808, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336446, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2936, 375703), numericProof := 75210, slack := 1}
noncomputable def case696 : PhysicalCase := ⟨1,169,.north,.push 143 (.stay 117),frame696⟩
theorem frame696_checked : CountedLocalCaseData.check data frame696 = true := by decide +kernel
theorem case696_fitted : fits case696 = true := by decide +kernel
noncomputable def frame697 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 19, changes := [(169, true), (143, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439687, afterBonus := 5832808, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336446, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (3540, 375705), numericProof := 75210, slack := 1}
noncomputable def case697 : PhysicalCase := ⟨1,117,.south,.push 143 (.stay 169),frame697⟩
theorem frame697_checked : CountedLocalCaseData.check data frame697 = true := by decide +kernel
theorem case697_fitted : fits case697 = true := by decide +kernel
noncomputable def frame698 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 19, changes := [(132, true), (158, false)], beforeBeta := 5439691, beforeBonus := 5832795, afterBeta := 5439693, afterBonus := 5832803, preBeta := 5440582, preBonus := 5833930, restrictionBeforeBeta := 926660, restrictionBeforeBonus := 1336466, restrictionAfterBeta := 926964, restrictionAfterBonus := 1336473, updateProofs := some (3812, 375722), numericProof := 75216, slack := 0}
noncomputable def case698 : PhysicalCase := ⟨1,184,.north,.push 158 (.stay 132),frame698⟩
theorem frame698_checked : CountedLocalCaseData.check data frame698 = true := by decide +kernel
theorem case698_fitted : fits case698 = true := by decide +kernel
noncomputable def frame699 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 19, changes := [(184, true), (158, false)], beforeBeta := 5439688, beforeBonus := 5832778, afterBeta := 5439693, afterBonus := 5832803, preBeta := 5439745, preBonus := 5833933, restrictionBeforeBeta := 927173, restrictionBeforeBonus := 1336487, restrictionAfterBeta := 927484, restrictionAfterBonus := 1336494, updateProofs := some (4487, 375740), numericProof := 75222, slack := 2}
noncomputable def case699 : PhysicalCase := ⟨1,132,.south,.push 158 (.stay 184),frame699⟩
theorem frame699_checked : CountedLocalCaseData.check data frame699 = true := by decide +kernel
theorem case699_fitted : fits case699 = true := by decide +kernel
noncomputable def frame700 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 19, changes := [(159, true), (158, false)], beforeBeta := 5439686, beforeBonus := 5832779, afterBeta := 5439693, afterBonus := 5832803, preBeta := 5440722, preBonus := 5833936, restrictionBeforeBeta := 927579, restrictionBeforeBonus := 1336513, restrictionAfterBeta := 927921, restrictionAfterBonus := 1336520, updateProofs := some (4902, 375758), numericProof := 75228, slack := 0}
noncomputable def case700 : PhysicalCase := ⟨1,157,.east,.push 158 (.stay 159),frame700⟩
theorem frame700_checked : CountedLocalCaseData.check data frame700 = true := by decide +kernel
theorem case700_fitted : fits case700 = true := by decide +kernel
noncomputable def frame701 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 19, changes := [(157, true), (158, false)], beforeBeta := 5439694, beforeBonus := 5832787, afterBeta := 5439693, afterBonus := 5832803, preBeta := 5439745, preBonus := 0, restrictionBeforeBeta := 928140, restrictionBeforeBonus := 1336541, restrictionAfterBeta := 928456, restrictionAfterBonus := 3, updateProofs := some (5209, 375776), numericProof := 75229, slack := 11}
noncomputable def case701 : PhysicalCase := ⟨1,159,.west,.push 158 (.stay 157),frame701⟩
theorem frame701_checked : CountedLocalCaseData.check data frame701 = true := by decide +kernel
theorem case701_fitted : fits case701 = true := by decide +kernel
noncomputable def frame702 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 19, changes := [(133, true), (159, false)], beforeBeta := 5439691, beforeBonus := 5832790, afterBeta := 5439694, afterBonus := 5832787, preBeta := 5440740, preBonus := 5833940, restrictionBeforeBeta := 928483, restrictionBeforeBonus := 1336561, restrictionAfterBeta := 928960, restrictionAfterBonus := 1336574, updateProofs := some (5531, 375796), numericProof := 75366, slack := 0}
noncomputable def case702 : PhysicalCase := ⟨1,185,.north,.push 159 (.stay 133),frame702⟩
theorem frame702_checked : CountedLocalCaseData.check data frame702 = true := by decide +kernel
theorem case702_fitted : fits case702 = true := by decide +kernel
noncomputable def frame703 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 19, changes := [(185, true), (159, false)], beforeBeta := 5439689, beforeBonus := 5832775, afterBeta := 5439694, afterBonus := 5832787, preBeta := 5439893, preBonus := 5833943, restrictionBeforeBeta := 929184, restrictionBeforeBonus := 1336593, restrictionAfterBeta := 929487, restrictionAfterBonus := 1336600, updateProofs := some (6289, 375817), numericProof := 75372, slack := 2}
noncomputable def case703 : PhysicalCase := ⟨1,133,.south,.push 159 (.stay 185),frame703⟩
theorem frame703_checked : CountedLocalCaseData.check data frame703 = true := by decide +kernel
theorem case703_fitted : fits case703 = true := by decide +kernel
noncomputable def frame704 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 19, changes := [(160, true), (159, false)], beforeBeta := 5439693, beforeBonus := 5832803, afterBeta := 5439694, afterBonus := 5832787, preBeta := 5440767, preBonus := 5833946, restrictionBeforeBeta := 929592, restrictionBeforeBonus := 1336618, restrictionAfterBeta := 929970, restrictionAfterBonus := 1336625, updateProofs := some (6753, 375838), numericProof := 75397, slack := 0}
noncomputable def case704 : PhysicalCase := ⟨1,158,.east,.push 159 (.stay 160),frame704⟩
theorem frame704_checked : CountedLocalCaseData.check data frame704 = true := by decide +kernel
theorem case704_fitted : fits case704 = true := by decide +kernel
noncomputable def frame705 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 19, changes := [(158, true), (159, false)], beforeBeta := 5439695, beforeBonus := 5832776, afterBeta := 5439694, afterBonus := 5832787, preBeta := 5440731, preBonus := 5833949, restrictionBeforeBeta := 930173, restrictionBeforeBonus := 1336646, restrictionAfterBeta := 930456, restrictionAfterBonus := 1336660, updateProofs := some (7150, 375859), numericProof := 75434, slack := 2}
noncomputable def case705 : PhysicalCase := ⟨1,160,.west,.push 159 (.stay 158),frame705⟩
theorem frame705_checked : CountedLocalCaseData.check data frame705 = true := by decide +kernel
theorem case705_fitted : fits case705 = true := by decide +kernel
noncomputable def frame706 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 19, changes := [(134, true), (160, false)], beforeBeta := 5439697, beforeBonus := 5832780, afterBeta := 5439695, afterBonus := 5832776, preBeta := 5440796, preBonus := 5833952, restrictionBeforeBeta := 930656, restrictionBeforeBonus := 1336682, restrictionAfterBeta := 931038, restrictionAfterBonus := 1336695, updateProofs := some (7485, 375880), numericProof := 75439, slack := 0}
noncomputable def case706 : PhysicalCase := ⟨1,186,.north,.push 160 (.stay 134),frame706⟩
theorem frame706_checked : CountedLocalCaseData.check data frame706 = true := by decide +kernel
theorem case706_fitted : fits case706 = true := by decide +kernel
noncomputable def frame707 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 19, changes := [(186, true), (160, false)], beforeBeta := 5112151, beforeBonus := 5832773, afterBeta := 5439695, afterBonus := 5832776, preBeta := 5439830, preBonus := 5833955, restrictionBeforeBeta := 931297, restrictionBeforeBonus := 1336708, restrictionAfterBeta := 931512, restrictionAfterBonus := 1336727, updateProofs := some (8273, 375901), numericProof := 75440, slack := 2}
noncomputable def case707 : PhysicalCase := ⟨1,134,.south,.push 160 (.stay 186),frame707⟩
theorem frame707_checked : CountedLocalCaseData.check data frame707 = true := by decide +kernel
theorem case707_fitted : fits case707 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
