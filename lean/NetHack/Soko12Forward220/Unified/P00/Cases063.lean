import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame756 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 20, changes := [(186, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832758, afterBeta := 5439691, afterBonus := 5832744, preBeta := 5440955, preBonus := 5833446, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1003417, restrictionAfterBeta := 946126, restrictionAfterBonus := 1003783, updateProofs := some (78819, 78745), numericProof := 45414, slack := 0}
noncomputable def case756 : PhysicalCase := ⟨0,238,.north,.push 212 (.stay 186),frame756⟩
theorem frame756_checked : CountedLocalCaseData.check data frame756 = true := by decide +kernel
theorem case756_fitted : fits case756 = true := by decide +kernel
noncomputable def frame757 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 20, changes := [(238, true), (212, false)], beforeBeta := 5439697, beforeBonus := 5832745, afterBeta := 5439691, afterBonus := 5832744, preBeta := 5439691, preBonus := 5833449, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1004918, restrictionAfterBeta := 79701, restrictionAfterBonus := 1005689, updateProofs := some (79946, 79872), numericProof := 45415, slack := 2}
noncomputable def case757 : PhysicalCase := ⟨0,186,.south,.push 212 (.stay 238),frame757⟩
theorem frame757_checked : CountedLocalCaseData.check data frame757 = true := by decide +kernel
theorem case757_fitted : fits case757 = true := by decide +kernel
noncomputable def frame758 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 20, changes := [(213, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832768, afterBeta := 5439691, afterBonus := 5832744, preBeta := 5439691, preBonus := 5833452, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1006867, restrictionAfterBeta := 8531, restrictionAfterBonus := 1007410, updateProofs := some (80993, 80919), numericProof := 45416, slack := 2}
noncomputable def case758 : PhysicalCase := ⟨0,211,.east,.push 212 (.stay 213),frame758⟩
theorem frame758_checked : CountedLocalCaseData.check data frame758 = true := by decide +kernel
theorem case758_fitted : fits case758 = true := by decide +kernel
noncomputable def frame759 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 20, changes := [(211, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832738, afterBeta := 5439691, afterBonus := 5832744, preBeta := 5439691, preBonus := 5833455, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1008755, restrictionAfterBeta := 8531, restrictionAfterBonus := 1009561, updateProofs := some (82020, 81946), numericProof := 45725, slack := 2}
noncomputable def case759 : PhysicalCase := ⟨0,213,.west,.push 212 (.stay 211),frame759⟩
theorem frame759_checked : CountedLocalCaseData.check data frame759 = true := by decide +kernel
theorem case759_fitted : fits case759 = true := by decide +kernel
noncomputable def frame760 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 20, changes := [(187, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832740, afterBeta := 5439691, afterBonus := 5832738, preBeta := 5441017, preBonus := 5833458, restrictionBeforeBeta := 98598, restrictionBeforeBonus := 1011363, restrictionAfterBeta := 1011364, restrictionAfterBonus := 1012286, updateProofs := some (83472, 83398), numericProof := 46162, slack := 2}
noncomputable def case760 : PhysicalCase := ⟨0,239,.north,.push 213 (.stay 187),frame760⟩
theorem frame760_checked : CountedLocalCaseData.check data frame760 = true := by decide +kernel
theorem case760_fitted : fits case760 = true := by decide +kernel
noncomputable def frame761 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 20, changes := [(239, true), (213, false)], beforeBeta := 5439698, beforeBonus := 5832739, afterBeta := 5439691, afterBonus := 5832738, preBeta := 5439691, preBonus := 5833461, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1013098, restrictionAfterBeta := 98598, restrictionAfterBonus := 1013237, updateProofs := some (85101, 85027), numericProof := 46163, slack := 2}
noncomputable def case761 : PhysicalCase := ⟨0,187,.south,.push 213 (.stay 239),frame761⟩
theorem frame761_checked : CountedLocalCaseData.check data frame761 = true := by decide +kernel
theorem case761_fitted : fits case761 = true := by decide +kernel
noncomputable def frame762 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 20, changes := [(214, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832744, afterBeta := 5439691, afterBonus := 5832738, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1014213, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (86561, 86487), numericProof := 46164, slack := 2}
noncomputable def case762 : PhysicalCase := ⟨0,212,.east,.push 213 (.stay 214),frame762⟩
theorem frame762_checked : CountedLocalCaseData.check data frame762 = true := by decide +kernel
theorem case762_fitted : fits case762 = true := by decide +kernel
noncomputable def frame763 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 20, changes := [(212, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832737, afterBeta := 5439691, afterBonus := 5832738, preBeta := 5439691, preBonus := 5833465, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1016192, restrictionAfterBeta := 8531, restrictionAfterBonus := 1017498, updateProofs := some (88021, 87947), numericProof := 46730, slack := 0}
noncomputable def case763 : PhysicalCase := ⟨0,214,.west,.push 213 (.stay 212),frame763⟩
theorem frame763_checked : CountedLocalCaseData.check data frame763 = true := by decide +kernel
theorem case763_fitted : fits case763 = true := by decide +kernel
noncomputable def frame764 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 20, changes := [(215, true), (214, false)], beforeBeta := 5439691, beforeBonus := 5832738, afterBeta := 5439691, afterBonus := 5832737, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1018883, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (90209, 90135), numericProof := 46731, slack := 2}
noncomputable def case764 : PhysicalCase := ⟨0,213,.east,.push 214 (.stay 215),frame764⟩
theorem frame764_checked : CountedLocalCaseData.check data frame764 = true := by decide +kernel
theorem case764_fitted : fits case764 = true := by decide +kernel
noncomputable def frame765 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 20, changes := [(213, true), (214, false)], beforeBeta := 5439691, beforeBonus := 5832734, afterBeta := 5439691, afterBonus := 5832737, preBeta := 5439691, preBonus := 5833468, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1021328, restrictionAfterBeta := 8531, restrictionAfterBonus := 1023163, updateProofs := some (92397, 92323), numericProof := 47547, slack := 0}
noncomputable def case765 : PhysicalCase := ⟨0,215,.west,.push 214 (.stay 213),frame765⟩
theorem frame765_checked : CountedLocalCaseData.check data frame765 = true := by decide +kernel
theorem case765_fitted : fits case765 = true := by decide +kernel
noncomputable def frame766 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 20, changes := [(189, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832734, preBeta := 5439691, preBonus := 5833395, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1025258, restrictionAfterBeta := 8531, restrictionAfterBonus := 1027163, updateProofs := some (94578, 94504), numericProof := 47548, slack := 2}
noncomputable def case766 : PhysicalCase := ⟨0,241,.north,.push 215 (.stay 189),frame766⟩
theorem frame766_checked : CountedLocalCaseData.check data frame766 = true := by decide +kernel
theorem case766_fitted : fits case766 = true := by decide +kernel
noncomputable def frame767 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 20, changes := [(241, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832736, afterBeta := 5439691, afterBonus := 5832734, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1028323, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (97695, 97621), numericProof := 47549, slack := 8}
noncomputable def case767 : PhysicalCase := ⟨0,189,.south,.push 215 (.stay 241),frame767⟩
theorem frame767_checked : CountedLocalCaseData.check data frame767 = true := by decide +kernel
theorem case767_fitted : fits case767 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
