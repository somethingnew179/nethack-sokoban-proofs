import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame756 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 18, changes := [(185, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832847, afterBeta := 5439691, afterBonus := 5832843, preBeta := 5439691, preBonus := 5834443, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341047, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341051, updateProofs := some (73977, 377793), numericProof := 76570, slack := 0}
noncomputable def case756 : PhysicalCase := ⟨2,237,.north,.push 211 (.stay 185),frame756⟩
theorem frame756_checked : CountedLocalCaseData.check data frame756 = true := by decide +kernel
theorem case756_fitted : fits case756 = true := by decide +kernel
noncomputable def frame757 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 18, changes := [(237, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832838, afterBeta := 5439691, afterBonus := 5832843, preBeta := 5439691, preBonus := 5834445, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341055, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341059, updateProofs := some (75362, 377800), numericProof := 76571, slack := 2}
noncomputable def case757 : PhysicalCase := ⟨2,185,.south,.push 211 (.stay 237),frame757⟩
theorem frame757_checked : CountedLocalCaseData.check data frame757 = true := by decide +kernel
theorem case757_fitted : fits case757 = true := by decide +kernel
noncomputable def frame758 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 18, changes := [(212, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832844, afterBeta := 5439691, afterBonus := 5832843, preBeta := 5439691, preBonus := 5834448, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341066, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341073, updateProofs := some (76625, 377807), numericProof := 76577, slack := 0}
noncomputable def case758 : PhysicalCase := ⟨2,210,.east,.push 211 (.stay 212),frame758⟩
theorem frame758_checked : CountedLocalCaseData.check data frame758 = true := by decide +kernel
theorem case758_fitted : fits case758 = true := by decide +kernel
noncomputable def frame759 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 18, changes := [(210, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832839, afterBeta := 5439691, afterBonus := 5832843, preBeta := 5439691, preBonus := 5834451, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341080, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341084, updateProofs := some (77839, 377814), numericProof := 76578, slack := 2}
noncomputable def case759 : PhysicalCase := ⟨2,212,.west,.push 211 (.stay 210),frame759⟩
theorem frame759_checked : CountedLocalCaseData.check data frame759 = true := by decide +kernel
theorem case759_fitted : fits case759 = true := by decide +kernel
noncomputable def frame760 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 18, changes := [(186, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832850, afterBeta := 5439691, afterBonus := 5832839, preBeta := 5440955, preBonus := 5834453, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1341091, restrictionAfterBeta := 946126, restrictionAfterBonus := 1341095, updateProofs := some (78819, 377821), numericProof := 76582, slack := 0}
noncomputable def case760 : PhysicalCase := ⟨2,238,.north,.push 212 (.stay 186),frame760⟩
theorem frame760_checked : CountedLocalCaseData.check data frame760 = true := by decide +kernel
theorem case760_fitted : fits case760 = true := by decide +kernel
noncomputable def frame761 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 18, changes := [(238, true), (212, false)], beforeBeta := 5439697, beforeBonus := 5832836, afterBeta := 5439691, afterBonus := 5832839, preBeta := 5439691, preBonus := 5834456, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1341099, restrictionAfterBeta := 79701, restrictionAfterBonus := 1341103, updateProofs := some (79946, 377828), numericProof := 76583, slack := 2}
noncomputable def case761 : PhysicalCase := ⟨2,186,.south,.push 212 (.stay 238),frame761⟩
theorem frame761_checked : CountedLocalCaseData.check data frame761 = true := by decide +kernel
theorem case761_fitted : fits case761 = true := by decide +kernel
noncomputable def frame762 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 18, changes := [(213, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832843, afterBeta := 5439691, afterBonus := 5832839, preBeta := 5439691, preBonus := 5834459, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341110, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341117, updateProofs := some (80993, 377835), numericProof := 76584, slack := 2}
noncomputable def case762 : PhysicalCase := ⟨2,211,.east,.push 212 (.stay 213),frame762⟩
theorem frame762_checked : CountedLocalCaseData.check data frame762 = true := by decide +kernel
theorem case762_fitted : fits case762 = true := by decide +kernel
noncomputable def frame763 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 18, changes := [(211, true), (212, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832839, preBeta := 5439691, preBonus := 5834461, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1341121, updateProofs := some (82020, 377842), numericProof := 76585, slack := 2}
noncomputable def case763 : PhysicalCase := ⟨2,213,.west,.push 212 (.stay 211),frame763⟩
theorem frame763_checked : CountedLocalCaseData.check data frame763 = true := by decide +kernel
theorem case763_fitted : fits case763 = true := by decide +kernel
noncomputable def frame764 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 18, changes := [(187, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832852, afterBeta := 5439691, afterBonus := 0, preBeta := 5441017, preBonus := 0, restrictionBeforeBeta := 98598, restrictionBeforeBonus := 1341128, restrictionAfterBeta := 1011364, restrictionAfterBonus := 3, updateProofs := some (83472, 82021), numericProof := 76586, slack := 2}
noncomputable def case764 : PhysicalCase := ⟨2,239,.north,.push 213 (.stay 187),frame764⟩
theorem frame764_checked : CountedLocalCaseData.check data frame764 = true := by decide +kernel
theorem case764_fitted : fits case764 = true := by decide +kernel
noncomputable def frame765 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 18, changes := [(239, true), (213, false)], beforeBeta := 5439698, beforeBonus := 5832837, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1341132, restrictionAfterBeta := 98598, restrictionAfterBonus := 3, updateProofs := some (85101, 83473), numericProof := 76587, slack := 2}
noncomputable def case765 : PhysicalCase := ⟨2,187,.south,.push 213 (.stay 239),frame765⟩
theorem frame765_checked : CountedLocalCaseData.check data frame765 = true := by decide +kernel
theorem case765_fitted : fits case765 = true := by decide +kernel
noncomputable def frame766 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 18, changes := [(214, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832839, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1341139, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (86561, 85102), numericProof := 76588, slack := 2}
noncomputable def case766 : PhysicalCase := ⟨2,212,.east,.push 213 (.stay 214),frame766⟩
theorem frame766_checked : CountedLocalCaseData.check data frame766 = true := by decide +kernel
theorem case766_fitted : fits case766 = true := by decide +kernel
noncomputable def frame767 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 18, changes := [(212, true), (213, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (88021, 86562), numericProof := 76589, slack := 0}
noncomputable def case767 : PhysicalCase := ⟨2,214,.west,.push 213 (.stay 212),frame767⟩
theorem frame767_checked : CountedLocalCaseData.check data frame767 = true := by decide +kernel
theorem case767_fitted : fits case767 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
