import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame696 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 20, changes := [(132, true), (158, false)], beforeBeta := 5439691, beforeBonus := 5832757, afterBeta := 5439693, afterBonus := 5832762, preBeta := 5440582, preBonus := 5833292, restrictionBeforeBeta := 926660, restrictionBeforeBonus := 926963, restrictionAfterBeta := 926964, restrictionAfterBonus := 927145, updateProofs := some (3812, 3787), numericProof := 12785, slack := 0}
noncomputable def case696 : PhysicalCase := ⟨0,184,.north,.push 158 (.stay 132),frame696⟩
theorem frame696_checked : CountedLocalCaseData.check data frame696 = true := by decide +kernel
theorem case696_fitted : fits case696 = true := by decide +kernel
noncomputable def frame697 : CountedLocalCase.Frame := {bindings := [(132, false), (158, true), (184, false)], budget := 20, changes := [(184, true), (158, false)], beforeBeta := 5439688, beforeBonus := 5832760, afterBeta := 5439693, afterBonus := 5832762, preBeta := 5439745, preBonus := 5833295, restrictionBeforeBeta := 927173, restrictionBeforeBonus := 927479, restrictionAfterBeta := 927484, restrictionAfterBonus := 927545, updateProofs := some (4487, 4428), numericProof := 13094, slack := 2}
noncomputable def case697 : PhysicalCase := ⟨0,132,.south,.push 158 (.stay 184),frame697⟩
theorem frame697_checked : CountedLocalCaseData.check data frame697 = true := by decide +kernel
theorem case697_fitted : fits case697 = true := by decide +kernel
noncomputable def frame698 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 20, changes := [(159, true), (158, false)], beforeBeta := 5439686, beforeBonus := 5832761, afterBeta := 5439693, afterBonus := 5832762, preBeta := 5440722, preBonus := 5833298, restrictionBeforeBeta := 927579, restrictionBeforeBonus := 927920, restrictionAfterBeta := 927921, restrictionAfterBonus := 928121, updateProofs := some (4902, 4858), numericProof := 13254, slack := 0}
noncomputable def case698 : PhysicalCase := ⟨0,157,.east,.push 158 (.stay 159),frame698⟩
theorem frame698_checked : CountedLocalCaseData.check data frame698 = true := by decide +kernel
theorem case698_fitted : fits case698 = true := by decide +kernel
noncomputable def frame699 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 20, changes := [(157, true), (158, false)], beforeBeta := 5439694, beforeBonus := 5832756, afterBeta := 5439693, afterBonus := 5832762, preBeta := 5439745, preBonus := 0, restrictionBeforeBeta := 928140, restrictionBeforeBonus := 928442, restrictionAfterBeta := 928456, restrictionAfterBonus := 3, updateProofs := some (5209, 5169), numericProof := 13255, slack := 11}
noncomputable def case699 : PhysicalCase := ⟨0,159,.west,.push 158 (.stay 157),frame699⟩
theorem frame699_checked : CountedLocalCaseData.check data frame699 = true := by decide +kernel
theorem case699_fitted : fits case699 = true := by decide +kernel
noncomputable def frame700 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 20, changes := [(133, true), (159, false)], beforeBeta := 5439691, beforeBonus := 5832748, afterBeta := 5439694, afterBonus := 5832756, preBeta := 5440740, preBonus := 5833302, restrictionBeforeBeta := 928483, restrictionBeforeBonus := 928959, restrictionAfterBeta := 928960, restrictionAfterBonus := 929170, updateProofs := some (5531, 5498), numericProof := 14618, slack := 0}
noncomputable def case700 : PhysicalCase := ⟨0,185,.north,.push 159 (.stay 133),frame700⟩
theorem frame700_checked : CountedLocalCaseData.check data frame700 = true := by decide +kernel
theorem case700_fitted : fits case700 = true := by decide +kernel
noncomputable def frame701 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 20, changes := [(185, true), (159, false)], beforeBeta := 5439689, beforeBonus := 5832755, afterBeta := 5439694, afterBonus := 5832756, preBeta := 5439893, preBonus := 5833305, restrictionBeforeBeta := 929184, restrictionBeforeBonus := 929480, restrictionAfterBeta := 929487, restrictionAfterBonus := 929554, updateProofs := some (6289, 6241), numericProof := 14784, slack := 2}
noncomputable def case701 : PhysicalCase := ⟨0,133,.south,.push 159 (.stay 185),frame701⟩
theorem frame701_checked : CountedLocalCaseData.check data frame701 = true := by decide +kernel
theorem case701_fitted : fits case701 = true := by decide +kernel
noncomputable def frame702 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 20, changes := [(160, true), (159, false)], beforeBeta := 5439693, beforeBonus := 5832762, afterBeta := 5439694, afterBonus := 5832756, preBeta := 5440767, preBonus := 5833308, restrictionBeforeBeta := 929592, restrictionBeforeBonus := 929953, restrictionAfterBeta := 929970, restrictionAfterBonus := 930165, updateProofs := some (6753, 6711), numericProof := 15264, slack := 0}
noncomputable def case702 : PhysicalCase := ⟨0,158,.east,.push 159 (.stay 160),frame702⟩
theorem frame702_checked : CountedLocalCaseData.check data frame702 = true := by decide +kernel
theorem case702_fitted : fits case702 = true := by decide +kernel
noncomputable def frame703 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 20, changes := [(158, true), (159, false)], beforeBeta := 5439695, beforeBonus := 5832747, afterBeta := 5439694, afterBonus := 5832756, preBeta := 5440731, preBonus := 5833311, restrictionBeforeBeta := 930173, restrictionBeforeBonus := 930451, restrictionAfterBeta := 930456, restrictionAfterBonus := 930631, updateProofs := some (7150, 7116), numericProof := 15401, slack := 2}
noncomputable def case703 : PhysicalCase := ⟨0,160,.west,.push 159 (.stay 158),frame703⟩
theorem frame703_checked : CountedLocalCaseData.check data frame703 = true := by decide +kernel
theorem case703_fitted : fits case703 = true := by decide +kernel
noncomputable def frame704 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 20, changes := [(134, true), (160, false)], beforeBeta := 5439697, beforeBonus := 5832745, afterBeta := 5439695, afterBonus := 5832747, preBeta := 5440796, preBonus := 5833314, restrictionBeforeBeta := 930656, restrictionBeforeBonus := 931037, restrictionAfterBeta := 931038, restrictionAfterBonus := 931286, updateProofs := some (7485, 7465), numericProof := 15933, slack := 0}
noncomputable def case704 : PhysicalCase := ⟨0,186,.north,.push 160 (.stay 134),frame704⟩
theorem frame704_checked : CountedLocalCaseData.check data frame704 = true := by decide +kernel
theorem case704_fitted : fits case704 = true := by decide +kernel
noncomputable def frame705 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 20, changes := [(186, true), (160, false)], beforeBeta := 5112151, beforeBonus := 5832752, afterBeta := 5439695, afterBonus := 5832747, preBeta := 5439830, preBonus := 5833317, restrictionBeforeBeta := 931297, restrictionBeforeBonus := 931503, restrictionAfterBeta := 931512, restrictionAfterBonus := 931616, updateProofs := some (8273, 8251), numericProof := 15934, slack := 2}
noncomputable def case705 : PhysicalCase := ⟨0,134,.south,.push 160 (.stay 186),frame705⟩
theorem frame705_checked : CountedLocalCaseData.check data frame705 = true := by decide +kernel
theorem case705_fitted : fits case705 = true := by decide +kernel
noncomputable def frame706 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 20, changes := [(161, true), (160, false)], beforeBeta := 5439694, beforeBonus := 5832756, afterBeta := 5439695, afterBonus := 5832747, preBeta := 5439830, preBonus := 5833320, restrictionBeforeBeta := 931651, restrictionBeforeBonus := 932073, restrictionAfterBeta := 932074, restrictionAfterBonus := 932110, updateProofs := some (8698, 8678), numericProof := 15935, slack := 6}
noncomputable def case706 : PhysicalCase := ⟨0,159,.east,.push 160 (.stay 161),frame706⟩
theorem frame706_checked : CountedLocalCaseData.check data frame706 = true := by decide +kernel
theorem case706_fitted : fits case706 = true := by decide +kernel
noncomputable def frame707 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 20, changes := [(159, true), (160, false)], beforeBeta := 5439690, beforeBonus := 5832753, afterBeta := 5439695, afterBonus := 5832747, preBeta := 5439830, preBonus := 5833322, restrictionBeforeBeta := 932129, restrictionBeforeBonus := 932453, restrictionAfterBeta := 932074, restrictionAfterBonus := 932651, updateProofs := some (9098, 9078), numericProof := 16478, slack := 2}
noncomputable def case707 : PhysicalCase := ⟨0,161,.west,.push 160 (.stay 159),frame707⟩
theorem frame707_checked : CountedLocalCaseData.check data frame707 = true := by decide +kernel
theorem case707_fitted : fits case707 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
