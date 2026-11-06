import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame708 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 19, changes := [(161, true), (160, false)], beforeBeta := 5439694, beforeBonus := 5832787, afterBeta := 5439695, afterBonus := 5832776, preBeta := 5439830, preBonus := 5833958, restrictionBeforeBeta := 931651, restrictionBeforeBonus := 1336748, restrictionAfterBeta := 932074, restrictionAfterBonus := 1336750, updateProofs := some (8698, 375922), numericProof := 75441, slack := 6}
noncomputable def case708 : PhysicalCase := ⟨1,159,.east,.push 160 (.stay 161),frame708⟩
theorem frame708_checked : CountedLocalCaseData.check data frame708 = true := by decide +kernel
theorem case708_fitted : fits case708 = true := by decide +kernel
noncomputable def frame709 : CountedLocalCase.Frame := {bindings := [(159, false), (160, true), (161, false)], budget := 19, changes := [(159, true), (160, false)], beforeBeta := 5439690, beforeBonus := 5832777, afterBeta := 5439695, afterBonus := 5832776, preBeta := 5439830, preBonus := 5833960, restrictionBeforeBeta := 932129, restrictionBeforeBonus := 1336764, restrictionAfterBeta := 932074, restrictionAfterBonus := 1336771, updateProofs := some (9098, 375943), numericProof := 75467, slack := 2}
noncomputable def case709 : PhysicalCase := ⟨1,161,.west,.push 160 (.stay 159),frame709⟩
theorem frame709_checked : CountedLocalCaseData.check data frame709 = true := by decide +kernel
theorem case709_fitted : fits case709 = true := by decide +kernel
noncomputable def frame710 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 19, changes := [(135, true), (161, false)], beforeBeta := 5439698, beforeBonus := 5832781, afterBeta := 5439690, afterBonus := 5832777, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1336778, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (9245, 375964), numericProof := 75468, slack := 8}
noncomputable def case710 : PhysicalCase := ⟨1,187,.north,.push 161 (.stay 135),frame710⟩
theorem frame710_checked : CountedLocalCaseData.check data frame710 = true := by decide +kernel
theorem case710_fitted : fits case710 = true := by decide +kernel
noncomputable def frame711 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 19, changes := [(187, true), (161, false)], beforeBeta := 5439690, beforeBonus := 5832774, afterBeta := 5439690, afterBonus := 5832777, preBeta := 5439690, preBonus := 5833964, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1336799, restrictionAfterBeta := 7685, restrictionAfterBonus := 1336820, updateProofs := some (10105, 375985), numericProof := 75472, slack := 0}
noncomputable def case711 : PhysicalCase := ⟨1,135,.south,.push 161 (.stay 187),frame711⟩
theorem frame711_checked : CountedLocalCaseData.check data frame711 = true := by decide +kernel
theorem case711_fitted : fits case711 = true := by decide +kernel
noncomputable def frame712 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 19, changes := [(140, true), (166, false)], beforeBeta := 5439699, beforeBonus := 5832791, afterBeta := 5439691, afterBonus := 5832792, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 1336822, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (10275, 375987), numericProof := 75473, slack := 3}
noncomputable def case712 : PhysicalCase := ⟨1,192,.north,.push 166 (.stay 140),frame712⟩
theorem frame712_checked : CountedLocalCaseData.check data frame712 = true := by decide +kernel
theorem case712_fitted : fits case712 = true := by decide +kernel
noncomputable def frame713 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 19, changes := [(192, true), (166, false)], beforeBeta := 5439691, beforeBonus := 5832800, afterBeta := 5439691, afterBonus := 5832792, preBeta := 5440852, preBonus := 5833967, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 1336824, restrictionAfterBeta := 935300, restrictionAfterBonus := 1336826, updateProofs := some (12136, 375989), numericProof := 75477, slack := 0}
noncomputable def case713 : PhysicalCase := ⟨1,140,.south,.push 166 (.stay 192),frame713⟩
theorem frame713_checked : CountedLocalCaseData.check data frame713 = true := by decide +kernel
theorem case713_fitted : fits case713 = true := by decide +kernel
noncomputable def frame714 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 19, changes := [(141, true), (167, false)], beforeBeta := 5439700, beforeBonus := 5832797, afterBeta := 5439691, afterBonus := 5832798, preBeta := 5440660, preBonus := 5833970, restrictionBeforeBeta := 935413, restrictionBeforeBonus := 1336828, restrictionAfterBeta := 935914, restrictionAfterBonus := 1336830, updateProofs := some (12436, 375991), numericProof := 75481, slack := 2}
noncomputable def case714 : PhysicalCase := ⟨1,193,.north,.push 167 (.stay 141),frame714⟩
theorem frame714_checked : CountedLocalCaseData.check data frame714 = true := by decide +kernel
theorem case714_fitted : fits case714 = true := by decide +kernel
noncomputable def frame715 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 19, changes := [(193, true), (167, false)], beforeBeta := 5439692, beforeBonus := 5832801, afterBeta := 5439691, afterBonus := 5832798, preBeta := 5440866, preBonus := 5833973, restrictionBeforeBeta := 936118, restrictionBeforeBonus := 1336832, restrictionAfterBeta := 936723, restrictionAfterBonus := 1336834, updateProofs := some (14425, 375993), numericProof := 75485, slack := 0}
noncomputable def case715 : PhysicalCase := ⟨1,141,.south,.push 167 (.stay 193),frame715⟩
theorem frame715_checked : CountedLocalCaseData.check data frame715 = true := by decide +kernel
theorem case715_fitted : fits case715 = true := by decide +kernel
noncomputable def frame716 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 19, changes := [(168, true), (167, false)], beforeBeta := 5439691, beforeBonus := 5832792, afterBeta := 5439691, afterBonus := 5832798, preBeta := 5440874, preBonus := 5833976, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 1336836, restrictionAfterBeta := 937363, restrictionAfterBonus := 1336838, updateProofs := some (15015, 375995), numericProof := 75489, slack := 2}
noncomputable def case716 : PhysicalCase := ⟨1,166,.east,.push 167 (.stay 168),frame716⟩
theorem frame716_checked : CountedLocalCaseData.check data frame716 = true := by decide +kernel
theorem case716_fitted : fits case716 = true := by decide +kernel
noncomputable def frame717 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 19, changes := [(166, true), (167, false)], beforeBeta := 5439696, beforeBonus := 5832805, afterBeta := 5439691, afterBonus := 5832798, preBeta := 5439691, preBonus := 5833979, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 1336840, restrictionAfterBeta := 14070, restrictionAfterBonus := 1336842, updateProofs := some (15520, 375997), numericProof := 75490, slack := 0}
noncomputable def case717 : PhysicalCase := ⟨1,168,.west,.push 167 (.stay 166),frame717⟩
theorem frame717_checked : CountedLocalCaseData.check data frame717 = true := by decide +kernel
theorem case717_fitted : fits case717 = true := by decide +kernel
noncomputable def frame718 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 19, changes := [(142, true), (168, false)], beforeBeta := 5439691, beforeBonus := 5832804, afterBeta := 5439696, afterBonus := 5832805, preBeta := 5439687, preBonus := 5833981, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 1336844, restrictionAfterBeta := 829, restrictionAfterBonus := 1336846, updateProofs := some (15994, 375999), numericProof := 75494, slack := 1}
noncomputable def case718 : PhysicalCase := ⟨1,194,.north,.push 168 (.stay 142),frame718⟩
theorem frame718_checked : CountedLocalCaseData.check data frame718 = true := by decide +kernel
theorem case718_fitted : fits case718 = true := by decide +kernel
noncomputable def frame719 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 19, changes := [(194, true), (168, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439696, afterBonus := 5832805, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (17937, 376001), numericProof := 75495, slack := 1}
noncomputable def case719 : PhysicalCase := ⟨1,142,.south,.push 168 (.stay 194),frame719⟩
theorem frame719_checked : CountedLocalCaseData.check data frame719 = true := by decide +kernel
theorem case719_fitted : fits case719 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
