import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame708 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 20, changes := [(135, true), (161, false)], beforeBeta := 5439698, beforeBonus := 5832739, afterBeta := 5439690, afterBonus := 5832753, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 933397, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (9245, 9215), numericProof := 16479, slack := 8}
noncomputable def case708 : PhysicalCase := ⟨0,187,.north,.push 161 (.stay 135),frame708⟩
theorem frame708_checked : CountedLocalCaseData.check data frame708 = true := by decide +kernel
theorem case708_fitted : fits case708 = true := by decide +kernel
noncomputable def frame709 : CountedLocalCase.Frame := {bindings := [(135, false), (161, true), (187, false)], budget := 20, changes := [(187, true), (161, false)], beforeBeta := 5439690, beforeBonus := 5832754, afterBeta := 5439690, afterBonus := 5832753, preBeta := 5439690, preBonus := 5833326, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 933789, restrictionAfterBeta := 7685, restrictionAfterBonus := 933924, updateProofs := some (10105, 10072), numericProof := 16567, slack := 0}
noncomputable def case709 : PhysicalCase := ⟨0,135,.south,.push 161 (.stay 187),frame709⟩
theorem frame709_checked : CountedLocalCaseData.check data frame709 = true := by decide +kernel
theorem case709_fitted : fits case709 = true := by decide +kernel
noncomputable def frame710 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 20, changes := [(140, true), (166, false)], beforeBeta := 5439699, beforeBonus := 5832721, afterBeta := 5439691, afterBonus := 5832723, preBeta := 5439691, preBonus := 5833329, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 934629, restrictionAfterBeta := 44389, restrictionAfterBonus := 934674, updateProofs := some (10275, 10217), numericProof := 16568, slack := 3}
noncomputable def case710 : PhysicalCase := ⟨0,192,.north,.push 166 (.stay 140),frame710⟩
theorem frame710_checked : CountedLocalCaseData.check data frame710 = true := by decide +kernel
theorem case710_fitted : fits case710 = true := by decide +kernel
noncomputable def frame711 : CountedLocalCase.Frame := {bindings := [(140, false), (166, true), (192, false)], budget := 20, changes := [(192, true), (166, false)], beforeBeta := 5439691, beforeBonus := 5832729, afterBeta := 5439691, afterBonus := 5832723, preBeta := 5440852, preBonus := 5833332, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 935299, restrictionAfterBeta := 935300, restrictionAfterBonus := 935393, updateProofs := some (12136, 12067), numericProof := 18283, slack := 0}
noncomputable def case711 : PhysicalCase := ⟨0,140,.south,.push 166 (.stay 192),frame711⟩
theorem frame711_checked : CountedLocalCaseData.check data frame711 = true := by decide +kernel
theorem case711_fitted : fits case711 = true := by decide +kernel
noncomputable def frame712 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 20, changes := [(141, true), (167, false)], beforeBeta := 5439700, beforeBonus := 5832719, afterBeta := 5439691, afterBonus := 5832726, preBeta := 5440660, preBonus := 5833335, restrictionBeforeBeta := 935413, restrictionBeforeBonus := 935902, restrictionAfterBeta := 935914, restrictionAfterBonus := 936098, updateProofs := some (12436, 12397), numericProof := 19509, slack := 2}
noncomputable def case712 : PhysicalCase := ⟨0,193,.north,.push 167 (.stay 141),frame712⟩
theorem frame712_checked : CountedLocalCaseData.check data frame712 = true := by decide +kernel
theorem case712_fitted : fits case712 = true := by decide +kernel
noncomputable def frame713 : CountedLocalCase.Frame := {bindings := [(141, false), (167, true), (193, false)], budget := 20, changes := [(193, true), (167, false)], beforeBeta := 5439692, beforeBonus := 5832733, afterBeta := 5439691, afterBonus := 5832726, preBeta := 5440866, preBonus := 5833338, restrictionBeforeBeta := 936118, restrictionBeforeBonus := 936695, restrictionAfterBeta := 936723, restrictionAfterBonus := 936832, updateProofs := some (14425, 14351), numericProof := 20598, slack := 0}
noncomputable def case713 : PhysicalCase := ⟨0,141,.south,.push 167 (.stay 193),frame713⟩
theorem frame713_checked : CountedLocalCaseData.check data frame713 = true := by decide +kernel
theorem case713_fitted : fits case713 = true := by decide +kernel
noncomputable def frame714 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 20, changes := [(168, true), (167, false)], beforeBeta := 5439691, beforeBonus := 5832723, afterBeta := 5439691, afterBonus := 5832726, preBeta := 5440874, preBonus := 5833341, restrictionBeforeBeta := 14070, restrictionBeforeBonus := 937362, restrictionAfterBeta := 937363, restrictionAfterBonus := 937573, updateProofs := some (15015, 14952), numericProof := 21632, slack := 2}
noncomputable def case714 : PhysicalCase := ⟨0,166,.east,.push 167 (.stay 168),frame714⟩
theorem frame714_checked : CountedLocalCaseData.check data frame714 = true := by decide +kernel
theorem case714_fitted : fits case714 = true := by decide +kernel
noncomputable def frame715 : CountedLocalCase.Frame := {bindings := [(166, false), (167, true), (168, false)], budget := 20, changes := [(166, true), (167, false)], beforeBeta := 5439696, beforeBonus := 5832722, afterBeta := 5439691, afterBonus := 5832726, preBeta := 5439691, preBonus := 5833344, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 937962, restrictionAfterBeta := 14070, restrictionAfterBonus := 938295, updateProofs := some (15520, 15462), numericProof := 21822, slack := 0}
noncomputable def case715 : PhysicalCase := ⟨0,168,.west,.push 167 (.stay 166),frame715⟩
theorem frame715_checked : CountedLocalCaseData.check data frame715 = true := by decide +kernel
theorem case715_fitted : fits case715 = true := by decide +kernel
noncomputable def frame716 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 20, changes := [(142, true), (168, false)], beforeBeta := 5439691, beforeBonus := 5832720, afterBeta := 5439696, afterBonus := 5832722, preBeta := 5439687, preBonus := 5833347, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 939223, restrictionAfterBeta := 829, restrictionAfterBonus := 939511, updateProofs := some (15994, 15931), numericProof := 23855, slack := 1}
noncomputable def case716 : PhysicalCase := ⟨0,194,.north,.push 168 (.stay 142),frame716⟩
theorem frame716_checked : CountedLocalCaseData.check data frame716 = true := by decide +kernel
theorem case716_fitted : fits case716 = true := by decide +kernel
noncomputable def frame717 : CountedLocalCase.Frame := {bindings := [(142, false), (168, true), (194, false)], budget := 20, changes := [(194, true), (168, false)], beforeBeta := 5439687, beforeBonus := 5832742, afterBeta := 5439696, afterBonus := 5832722, preBeta := 5439687, preBonus := 5833350, restrictionBeforeBeta := 829, restrictionBeforeBonus := 939865, restrictionAfterBeta := 829, restrictionAfterBonus := 939886, updateProofs := some (17937, 17869), numericProof := 24185, slack := 1}
noncomputable def case717 : PhysicalCase := ⟨0,142,.south,.push 168 (.stay 194),frame717⟩
theorem frame717_checked : CountedLocalCaseData.check data frame717 = true := by decide +kernel
theorem case717_fitted : fits case717 = true := by decide +kernel
noncomputable def frame718 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 20, changes := [(169, true), (168, false)], beforeBeta := 5439691, beforeBonus := 5832726, afterBeta := 5439696, afterBonus := 5832722, preBeta := 5439687, preBonus := 5833353, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 940392, restrictionAfterBeta := 829, restrictionAfterBonus := 940465, updateProofs := some (18552, 18489), numericProof := 24616, slack := 1}
noncomputable def case718 : PhysicalCase := ⟨0,167,.east,.push 168 (.stay 169),frame718⟩
theorem frame718_checked : CountedLocalCaseData.check data frame718 = true := by decide +kernel
theorem case718_fitted : fits case718 = true := by decide +kernel
noncomputable def frame719 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 20, changes := [(167, true), (168, false)], beforeBeta := 5439687, beforeBonus := 5832725, afterBeta := 5439696, afterBonus := 5832722, preBeta := 5439687, preBonus := 5833356, restrictionBeforeBeta := 829, restrictionBeforeBonus := 940919, restrictionAfterBeta := 829, restrictionAfterBonus := 941269, updateProofs := some (19099, 19036), numericProof := 25741, slack := 0}
noncomputable def case719 : PhysicalCase := ⟨0,169,.west,.push 168 (.stay 167),frame719⟩
theorem frame719_checked : CountedLocalCaseData.check data frame719 = true := by decide +kernel
theorem case719_fitted : fits case719 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
