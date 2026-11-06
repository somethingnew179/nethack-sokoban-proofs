import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame708 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 16, changes := [(133, true), (159, false)], beforeBeta := 5439691, beforeBonus := 5832895, afterBeta := 5439694, afterBonus := 5832889, preBeta := 5440740, preBonus := 5835005, restrictionBeforeBeta := 928483, restrictionBeforeBonus := 1344231, restrictionAfterBeta := 928960, restrictionAfterBonus := 1344234, updateProofs := some (5531, 378667), numericProof := 77637, slack := 0}
noncomputable def case708 : PhysicalCase := ⟨4,185,.north,.push 159 (.stay 133),frame708⟩
theorem frame708_checked : CountedLocalCaseData.check data frame708 = true := by decide +kernel
theorem case708_fitted : fits case708 = true := by decide +kernel
noncomputable def frame709 : CountedLocalCase.Frame := {bindings := [(133, false), (159, true), (185, false)], budget := 16, changes := [(185, true), (159, false)], beforeBeta := 5439689, beforeBonus := 5832888, afterBeta := 5439694, afterBonus := 5832889, preBeta := 5439893, preBonus := 5835008, restrictionBeforeBeta := 929184, restrictionBeforeBonus := 1344237, restrictionAfterBeta := 929487, restrictionAfterBonus := 1344239, updateProofs := some (6289, 378670), numericProof := 77638, slack := 2}
noncomputable def case709 : PhysicalCase := ⟨4,133,.south,.push 159 (.stay 185),frame709⟩
theorem frame709_checked : CountedLocalCaseData.check data frame709 = true := by decide +kernel
theorem case709_fitted : fits case709 = true := by decide +kernel
noncomputable def frame710 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 16, changes := [(160, true), (159, false)], beforeBeta := 5439693, beforeBonus := 5832892, afterBeta := 5439694, afterBonus := 5832889, preBeta := 5440767, preBonus := 5835009, restrictionBeforeBeta := 929592, restrictionBeforeBonus := 1344242, restrictionAfterBeta := 929970, restrictionAfterBonus := 1344244, updateProofs := some (6753, 378673), numericProof := 77642, slack := 0}
noncomputable def case710 : PhysicalCase := ⟨4,158,.east,.push 159 (.stay 160),frame710⟩
theorem frame710_checked : CountedLocalCaseData.check data frame710 = true := by decide +kernel
theorem case710_fitted : fits case710 = true := by decide +kernel
noncomputable def frame711 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 16, changes := [(158, true), (159, false)], beforeBeta := 5439695, beforeBonus := 5832887, afterBeta := 5439694, afterBonus := 5832889, preBeta := 5440731, preBonus := 5835011, restrictionBeforeBeta := 930173, restrictionBeforeBonus := 1344247, restrictionAfterBeta := 930456, restrictionAfterBonus := 1344250, updateProofs := some (7150, 378676), numericProof := 77647, slack := 2}
noncomputable def case711 : PhysicalCase := ⟨4,160,.west,.push 159 (.stay 158),frame711⟩
theorem frame711_checked : CountedLocalCaseData.check data frame711 = true := by decide +kernel
theorem case711_fitted : fits case711 = true := by decide +kernel
noncomputable def frame712 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 16, changes := [(134, true), (160, false)], beforeBeta := 5439697, beforeBonus := 5832893, afterBeta := 5439695, afterBonus := 5832887, preBeta := 5440796, preBonus := 5835013, restrictionBeforeBeta := 930656, restrictionBeforeBonus := 1344253, restrictionAfterBeta := 931038, restrictionAfterBonus := 1344255, updateProofs := some (7485, 378679), numericProof := 77648, slack := 0}
noncomputable def case712 : PhysicalCase := ⟨4,186,.north,.push 160 (.stay 134),frame712⟩
theorem frame712_checked : CountedLocalCaseData.check data frame712 = true := by decide +kernel
theorem case712_fitted : fits case712 = true := by decide +kernel
noncomputable def frame713 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 16, changes := [(186, true), (160, false)], beforeBeta := 5112151, beforeBonus := 5832886, afterBeta := 5439695, afterBonus := 5832887, preBeta := 5439830, preBonus := 5835015, restrictionBeforeBeta := 931297, restrictionBeforeBonus := 1344258, restrictionAfterBeta := 931512, restrictionAfterBonus := 1344261, updateProofs := some (8273, 378682), numericProof := 77649, slack := 2}
noncomputable def case713 : PhysicalCase := ⟨4,134,.south,.push 160 (.stay 186),frame713⟩
theorem frame713_checked : CountedLocalCaseData.check data frame713 = true := by decide +kernel
theorem case713_fitted : fits case713 = true := by decide +kernel
noncomputable def frame714 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 16, changes := [(161, true), (160, false)], beforeBeta := 5439694, beforeBonus := 5832889, afterBeta := 5439695, afterBonus := 5832887, preBeta := 5439830, preBonus := 0, restrictionBeforeBeta := 931651, restrictionBeforeBonus := 1344264, restrictionAfterBeta := 932074, restrictionAfterBonus := 3, updateProofs := some (8698, 378685), numericProof := 77650, slack := 6}
noncomputable def case714 : PhysicalCase := ⟨4,159,.east,.push 160 (.stay 161),frame714⟩
theorem frame714_checked : CountedLocalCaseData.check data frame714 = true := by decide +kernel
theorem case714_fitted : fits case714 = true := by decide +kernel
noncomputable def frame715 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 16, changes := [(159, true), (160, false)], beforeBeta := 5439690, beforeBonus := 5832887, afterBeta := 5439695, afterBonus := 5832887, preBeta := 5439830, preBonus := 5835018, restrictionBeforeBeta := 932129, restrictionBeforeBonus := 1344266, restrictionAfterBeta := 932074, restrictionAfterBonus := 1344268, updateProofs := some (9098, 378688), numericProof := 77654, slack := 2}
noncomputable def case715 : PhysicalCase := ⟨4,161,.west,.push 160 (.stay 159),frame715⟩
theorem frame715_checked : CountedLocalCaseData.check data frame715 = true := by decide +kernel
theorem case715_fitted : fits case715 = true := by decide +kernel
noncomputable def frame716 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 16, changes := [(135, true), (161, false)], beforeBeta := 5439698, beforeBonus := 5832894, afterBeta := 5439690, afterBonus := 5832887, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1344270, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (9245, 378691), numericProof := 77655, slack := 8}
noncomputable def case716 : PhysicalCase := ⟨4,187,.north,.push 161 (.stay 135),frame716⟩
theorem frame716_checked : CountedLocalCaseData.check data frame716 = true := by decide +kernel
theorem case716_fitted : fits case716 = true := by decide +kernel
noncomputable def frame717 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 16, changes := [(187, true), (161, false)], beforeBeta := 5439690, beforeBonus := 5832887, afterBeta := 5439690, afterBonus := 5832887, preBeta := 5439690, preBonus := 5835020, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1344273, restrictionAfterBeta := 7685, restrictionAfterBonus := 1344276, updateProofs := some (10105, 378694), numericProof := 77656, slack := 0}
noncomputable def case717 : PhysicalCase := ⟨4,135,.south,.push 161 (.stay 187),frame717⟩
theorem frame717_checked : CountedLocalCaseData.check data frame717 = true := by decide +kernel
theorem case717_fitted : fits case717 = true := by decide +kernel
noncomputable def frame718 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 16, changes := [(140, true), (166, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (10275, 10106), numericProof := 77657, slack := 3}
noncomputable def case718 : PhysicalCase := ⟨4,192,.north,.push 166 (.stay 140),frame718⟩
theorem frame718_checked : CountedLocalCaseData.check data frame718 = true := by decide +kernel
theorem case718_fitted : fits case718 = true := by decide +kernel
noncomputable def frame719 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 16, changes := [(192, true), (166, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (12136, 10276), numericProof := 77658, slack := 0}
noncomputable def case719 : PhysicalCase := ⟨4,140,.south,.push 166 (.stay 192),frame719⟩
theorem frame719_checked : CountedLocalCaseData.check data frame719 = true := by decide +kernel
theorem case719_fitted : fits case719 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
