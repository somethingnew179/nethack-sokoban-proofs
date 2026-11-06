import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame708 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 17, changes := [(160, true), (159, false)], beforeBeta := 5439693, beforeBonus := 5832863, afterBeta := 5439694, afterBonus := 5832862, preBeta := 5440767, preBonus := 5834713, restrictionBeforeBeta := 929592, restrictionBeforeBonus := 1342844, restrictionAfterBeta := 929970, restrictionAfterBonus := 1342847, updateProofs := some (6753, 378286), numericProof := 77085, slack := 0}
noncomputable def case708 : PhysicalCase := ⟨3,158,.east,.push 159 (.stay 160),frame708⟩
theorem frame708_checked : CountedLocalCaseData.check data frame708 = true := by decide +kernel
theorem case708_fitted : fits case708 = true := by decide +kernel
noncomputable def frame709 : CountedLocalCase.Frame := {bindings := [(158, false), (159, true), (160, false)], budget := 17, changes := [(158, true), (159, false)], beforeBeta := 5439695, beforeBonus := 5832861, afterBeta := 5439694, afterBonus := 5832862, preBeta := 5440731, preBonus := 5834716, restrictionBeforeBeta := 930173, restrictionBeforeBonus := 1342851, restrictionAfterBeta := 930456, restrictionAfterBonus := 1342855, updateProofs := some (7150, 378290), numericProof := 77091, slack := 2}
noncomputable def case709 : PhysicalCase := ⟨3,160,.west,.push 159 (.stay 158),frame709⟩
theorem frame709_checked : CountedLocalCaseData.check data frame709 = true := by decide +kernel
theorem case709_fitted : fits case709 = true := by decide +kernel
noncomputable def frame710 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 17, changes := [(134, true), (160, false)], beforeBeta := 5439697, beforeBonus := 5832864, afterBeta := 5439695, afterBonus := 5832861, preBeta := 5440796, preBonus := 5834719, restrictionBeforeBeta := 930656, restrictionBeforeBonus := 1342859, restrictionAfterBeta := 931038, restrictionAfterBonus := 1342862, updateProofs := some (7485, 378294), numericProof := 77092, slack := 0}
noncomputable def case710 : PhysicalCase := ⟨3,186,.north,.push 160 (.stay 134),frame710⟩
theorem frame710_checked : CountedLocalCaseData.check data frame710 = true := by decide +kernel
theorem case710_fitted : fits case710 = true := by decide +kernel
noncomputable def frame711 : CountedLocalCase.Frame := {bindings := [(134, false), (160, true), (186, false)], budget := 17, changes := [(186, true), (160, false)], beforeBeta := 5112151, beforeBonus := 5832858, afterBeta := 5439695, afterBonus := 5832861, preBeta := 5439830, preBonus := 5834721, restrictionBeforeBeta := 931297, restrictionBeforeBonus := 1342866, restrictionAfterBeta := 931512, restrictionAfterBonus := 1342870, updateProofs := some (8273, 378298), numericProof := 77093, slack := 2}
noncomputable def case711 : PhysicalCase := ⟨3,134,.south,.push 160 (.stay 186),frame711⟩
theorem frame711_checked : CountedLocalCaseData.check data frame711 = true := by decide +kernel
theorem case711_fitted : fits case711 = true := by decide +kernel
noncomputable def frame712 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 17, changes := [(161, true), (160, false)], beforeBeta := 5439694, beforeBonus := 5832862, afterBeta := 5439695, afterBonus := 5832861, preBeta := 5439830, preBonus := 0, restrictionBeforeBeta := 931651, restrictionBeforeBonus := 1342874, restrictionAfterBeta := 932074, restrictionAfterBonus := 3, updateProofs := some (8698, 378302), numericProof := 77094, slack := 6}
noncomputable def case712 : PhysicalCase := ⟨3,159,.east,.push 160 (.stay 161),frame712⟩
theorem frame712_checked : CountedLocalCaseData.check data frame712 = true := by decide +kernel
theorem case712_fitted : fits case712 = true := by decide +kernel
noncomputable def frame713 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 17, changes := [(159, true), (160, false)], beforeBeta := 5439690, beforeBonus := 5832859, afterBeta := 5439695, afterBonus := 5832861, preBeta := 5439830, preBonus := 5834725, restrictionBeforeBeta := 932129, restrictionBeforeBonus := 1342877, restrictionAfterBeta := 932074, restrictionAfterBonus := 1342880, updateProofs := some (9098, 378306), numericProof := 77099, slack := 2}
noncomputable def case713 : PhysicalCase := ⟨3,161,.west,.push 160 (.stay 159),frame713⟩
theorem frame713_checked : CountedLocalCaseData.check data frame713 = true := by decide +kernel
theorem case713_fitted : fits case713 = true := by decide +kernel
noncomputable def frame714 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 17, changes := [(135, true), (161, false)], beforeBeta := 5439698, beforeBonus := 5832865, afterBeta := 5439690, afterBonus := 5832859, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1342883, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (9245, 378310), numericProof := 77100, slack := 8}
noncomputable def case714 : PhysicalCase := ⟨3,187,.north,.push 161 (.stay 135),frame714⟩
theorem frame714_checked : CountedLocalCaseData.check data frame714 = true := by decide +kernel
theorem case714_fitted : fits case714 = true := by decide +kernel
noncomputable def frame715 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 17, changes := [(187, true), (161, false)], beforeBeta := 5439690, beforeBonus := 5832859, afterBeta := 5439690, afterBonus := 5832859, preBeta := 5439690, preBonus := 5834728, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1342887, restrictionAfterBeta := 7685, restrictionAfterBonus := 1342891, updateProofs := some (10105, 378314), numericProof := 77101, slack := 0}
noncomputable def case715 : PhysicalCase := ⟨3,135,.south,.push 161 (.stay 187),frame715⟩
theorem frame715_checked : CountedLocalCaseData.check data frame715 = true := by decide +kernel
theorem case715_fitted : fits case715 = true := by decide +kernel
noncomputable def frame716 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 17, changes := [(140, true), (166, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (10275, 10106), numericProof := 77102, slack := 3}
noncomputable def case716 : PhysicalCase := ⟨3,192,.north,.push 166 (.stay 140),frame716⟩
theorem frame716_checked : CountedLocalCaseData.check data frame716 = true := by decide +kernel
theorem case716_fitted : fits case716 = true := by decide +kernel
noncomputable def frame717 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 17, changes := [(192, true), (166, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (12136, 10276), numericProof := 77103, slack := 0}
noncomputable def case717 : PhysicalCase := ⟨3,140,.south,.push 166 (.stay 192),frame717⟩
theorem frame717_checked : CountedLocalCaseData.check data frame717 = true := by decide +kernel
theorem case717_fitted : fits case717 = true := by decide +kernel
noncomputable def frame718 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 17, changes := [(141, true), (167, false)], beforeBeta := 5439700, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440660, preBonus := 0, restrictionBeforeBeta := 935413, restrictionBeforeBonus := 3, restrictionAfterBeta := 935914, restrictionAfterBonus := 3, updateProofs := some (12436, 12137), numericProof := 77104, slack := 2}
noncomputable def case718 : PhysicalCase := ⟨3,193,.north,.push 167 (.stay 141),frame718⟩
theorem frame718_checked : CountedLocalCaseData.check data frame718 = true := by decide +kernel
theorem case718_fitted : fits case718 = true := by decide +kernel
noncomputable def frame719 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 17, changes := [(193, true), (167, false)], beforeBeta := 5439692, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440866, preBonus := 0, restrictionBeforeBeta := 936118, restrictionBeforeBonus := 3, restrictionAfterBeta := 936723, restrictionAfterBonus := 3, updateProofs := some (14425, 12437), numericProof := 77105, slack := 0}
noncomputable def case719 : PhysicalCase := ⟨3,141,.south,.push 167 (.stay 193),frame719⟩
theorem frame719_checked : CountedLocalCaseData.check data frame719 = true := by decide +kernel
theorem case719_fitted : fits case719 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
