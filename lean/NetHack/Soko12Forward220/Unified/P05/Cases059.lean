import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame708 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 15, changes := [(159, true), (158, false)], beforeBeta := 5439686, beforeBonus := 5832910, afterBeta := 5439693, afterBonus := 5832910, preBeta := 5440722, preBonus := 0, restrictionBeforeBeta := 927579, restrictionBeforeBonus := 1345068, restrictionAfterBeta := 927921, restrictionAfterBonus := 3, updateProofs := some (4902, 378945), numericProof := 78164, slack := 0}
noncomputable def case708 : PhysicalCase := ⟨5,157,.east,.push 158 (.stay 159),frame708⟩
theorem frame708_checked : CountedLocalCaseData.check data frame708 = true := by decide +kernel
theorem case708_fitted : fits case708 = true := by decide +kernel
noncomputable def frame709 : CountedLocalCase.Frame := {bindings := [(157, false), (158, true), (159, false)], budget := 15, changes := [(157, true), (158, false)], beforeBeta := 5439694, beforeBonus := 5832909, afterBeta := 5439693, afterBonus := 5832910, preBeta := 5439745, preBonus := 0, restrictionBeforeBeta := 928140, restrictionBeforeBonus := 1345070, restrictionAfterBeta := 928456, restrictionAfterBonus := 3, updateProofs := some (5209, 378947), numericProof := 78165, slack := 11}
noncomputable def case709 : PhysicalCase := ⟨5,159,.west,.push 158 (.stay 157),frame709⟩
theorem frame709_checked : CountedLocalCaseData.check data frame709 = true := by decide +kernel
theorem case709_fitted : fits case709 = true := by decide +kernel
noncomputable def frame710 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 15, changes := [(133, true), (159, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439694, afterBonus := 5832909, preBeta := 5440740, preBonus := 5835232, restrictionBeforeBeta := 928483, restrictionBeforeBonus := 1345072, restrictionAfterBeta := 928960, restrictionAfterBonus := 1345074, updateProofs := some (5531, 378949), numericProof := 78169, slack := 0}
noncomputable def case710 : PhysicalCase := ⟨5,185,.north,.push 159 (.stay 133),frame710⟩
theorem frame710_checked : CountedLocalCaseData.check data frame710 = true := by decide +kernel
theorem case710_fitted : fits case710 = true := by decide +kernel
noncomputable def frame711 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 15, changes := [(185, true), (159, false)], beforeBeta := 5439689, beforeBonus := 5832910, afterBeta := 5439694, afterBonus := 5832909, preBeta := 5439893, preBonus := 0, restrictionBeforeBeta := 929184, restrictionBeforeBonus := 1345076, restrictionAfterBeta := 929487, restrictionAfterBonus := 3, updateProofs := some (6289, 378951), numericProof := 78170, slack := 2}
noncomputable def case711 : PhysicalCase := ⟨5,133,.south,.push 159 (.stay 185),frame711⟩
theorem frame711_checked : CountedLocalCaseData.check data frame711 = true := by decide +kernel
theorem case711_fitted : fits case711 = true := by decide +kernel
noncomputable def frame712 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 15, changes := [(160, true), (159, false)], beforeBeta := 5439693, beforeBonus := 5832910, afterBeta := 5439694, afterBonus := 5832909, preBeta := 5440767, preBonus := 0, restrictionBeforeBeta := 929592, restrictionBeforeBonus := 1345078, restrictionAfterBeta := 929970, restrictionAfterBonus := 3, updateProofs := some (6753, 378953), numericProof := 78171, slack := 0}
noncomputable def case712 : PhysicalCase := ⟨5,158,.east,.push 159 (.stay 160),frame712⟩
theorem frame712_checked : CountedLocalCaseData.check data frame712 = true := by decide +kernel
theorem case712_fitted : fits case712 = true := by decide +kernel
noncomputable def frame713 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 15, changes := [(158, true), (159, false)], beforeBeta := 5439695, beforeBonus := 5832909, afterBeta := 5439694, afterBonus := 5832909, preBeta := 5440731, preBonus := 5835234, restrictionBeforeBeta := 930173, restrictionBeforeBonus := 1345080, restrictionAfterBeta := 930456, restrictionAfterBonus := 1345082, updateProofs := some (7150, 378955), numericProof := 78175, slack := 2}
noncomputable def case713 : PhysicalCase := ⟨5,160,.west,.push 159 (.stay 158),frame713⟩
theorem frame713_checked : CountedLocalCaseData.check data frame713 = true := by decide +kernel
theorem case713_fitted : fits case713 = true := by decide +kernel
noncomputable def frame714 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 15, changes := [(134, true), (160, false)], beforeBeta := 5439697, beforeBonus := 5832911, afterBeta := 5439695, afterBonus := 5832909, preBeta := 5440796, preBonus := 0, restrictionBeforeBeta := 930656, restrictionBeforeBonus := 1345084, restrictionAfterBeta := 931038, restrictionAfterBonus := 3, updateProofs := some (7485, 378957), numericProof := 78176, slack := 0}
noncomputable def case714 : PhysicalCase := ⟨5,186,.north,.push 160 (.stay 134),frame714⟩
theorem frame714_checked : CountedLocalCaseData.check data frame714 = true := by decide +kernel
theorem case714_fitted : fits case714 = true := by decide +kernel
noncomputable def frame715 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 15, changes := [(186, true), (160, false)], beforeBeta := 5112151, beforeBonus := 5832909, afterBeta := 5439695, afterBonus := 5832909, preBeta := 5439830, preBonus := 5835236, restrictionBeforeBeta := 931297, restrictionBeforeBonus := 1345086, restrictionAfterBeta := 931512, restrictionAfterBonus := 1345088, updateProofs := some (8273, 378959), numericProof := 78177, slack := 2}
noncomputable def case715 : PhysicalCase := ⟨5,134,.south,.push 160 (.stay 186),frame715⟩
theorem frame715_checked : CountedLocalCaseData.check data frame715 = true := by decide +kernel
theorem case715_fitted : fits case715 = true := by decide +kernel
noncomputable def frame716 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 15, changes := [(161, true), (160, false)], beforeBeta := 5439694, beforeBonus := 5832909, afterBeta := 5439695, afterBonus := 5832909, preBeta := 5439830, preBonus := 0, restrictionBeforeBeta := 931651, restrictionBeforeBonus := 1345090, restrictionAfterBeta := 932074, restrictionAfterBonus := 3, updateProofs := some (8698, 378961), numericProof := 78178, slack := 6}
noncomputable def case716 : PhysicalCase := ⟨5,159,.east,.push 160 (.stay 161),frame716⟩
theorem frame716_checked : CountedLocalCaseData.check data frame716 = true := by decide +kernel
theorem case716_fitted : fits case716 = true := by decide +kernel
noncomputable def frame717 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 15, changes := [(159, true), (160, false)], beforeBeta := 5439690, beforeBonus := 5832909, afterBeta := 5439695, afterBonus := 5832909, preBeta := 5439830, preBonus := 0, restrictionBeforeBeta := 932129, restrictionBeforeBonus := 1345090, restrictionAfterBeta := 932074, restrictionAfterBonus := 3, updateProofs := some (9098, 378963), numericProof := 78179, slack := 2}
noncomputable def case717 : PhysicalCase := ⟨5,161,.west,.push 160 (.stay 159),frame717⟩
theorem frame717_checked : CountedLocalCaseData.check data frame717 = true := by decide +kernel
theorem case717_fitted : fits case717 = true := by decide +kernel
noncomputable def frame718 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 15, changes := [(135, true), (161, false)], beforeBeta := 5439698, beforeBonus := 0, afterBeta := 5439690, afterBonus := 5832909, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 3, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (9245, 378965), numericProof := 78180, slack := 8}
noncomputable def case718 : PhysicalCase := ⟨5,187,.north,.push 161 (.stay 135),frame718⟩
theorem frame718_checked : CountedLocalCaseData.check data frame718 = true := by decide +kernel
theorem case718_fitted : fits case718 = true := by decide +kernel
noncomputable def frame719 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 15, changes := [(187, true), (161, false)], beforeBeta := 5439690, beforeBonus := 5832909, afterBeta := 5439690, afterBonus := 5832909, preBeta := 5439690, preBonus := 5835238, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1345092, restrictionAfterBeta := 7685, restrictionAfterBonus := 1345094, updateProofs := some (10105, 378967), numericProof := 78181, slack := 0}
noncomputable def case719 : PhysicalCase := ⟨5,135,.south,.push 161 (.stay 187),frame719⟩
theorem frame719_checked : CountedLocalCaseData.check data frame719 = true := by decide +kernel
theorem case719_fitted : fits case719 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
