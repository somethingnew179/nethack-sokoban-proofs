import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame756 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 17, changes := [(184, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832873, afterBeta := 5439691, afterBonus := 5832874, preBeta := 5439691, preBonus := 5834757, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1342973, restrictionAfterBeta := 8531, restrictionAfterBonus := 1342977, updateProofs := some (71708, 378364), numericProof := 77163, slack := 0}
noncomputable def case756 : PhysicalCase := ⟨3,236,.north,.push 210 (.stay 184),frame756⟩
theorem frame756_checked : CountedLocalCaseData.check data frame756 = true := by decide +kernel
theorem case756_fitted : fits case756 = true := by decide +kernel
noncomputable def frame757 : CountedLocalCase.Frame := {bindings := [(184, false), (210, true), (236, false)], budget := 17, changes := [(236, true), (210, false)], beforeBeta := 5439691, beforeBonus := 5832867, afterBeta := 5439691, afterBonus := 5832874, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1342981, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (72918, 378368), numericProof := 77164, slack := 2}
noncomputable def case757 : PhysicalCase := ⟨3,184,.south,.push 210 (.stay 236),frame757⟩
theorem frame757_checked : CountedLocalCaseData.check data frame757 = true := by decide +kernel
theorem case757_fitted : fits case757 = true := by decide +kernel
noncomputable def frame758 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 17, changes := [(185, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832872, afterBeta := 5439691, afterBonus := 5832871, preBeta := 5439691, preBonus := 5834761, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1342985, restrictionAfterBeta := 8531, restrictionAfterBonus := 1342988, updateProofs := some (73977, 378372), numericProof := 77165, slack := 0}
noncomputable def case758 : PhysicalCase := ⟨3,237,.north,.push 211 (.stay 185),frame758⟩
theorem frame758_checked : CountedLocalCaseData.check data frame758 = true := by decide +kernel
theorem case758_fitted : fits case758 = true := by decide +kernel
noncomputable def frame759 : CountedLocalCase.Frame := {bindings := [(185, false), (211, true), (237, false)], budget := 17, changes := [(237, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832866, afterBeta := 5439691, afterBonus := 5832871, preBeta := 5439691, preBonus := 5834763, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1342991, restrictionAfterBeta := 8531, restrictionAfterBonus := 1342994, updateProofs := some (75362, 378376), numericProof := 77166, slack := 2}
noncomputable def case759 : PhysicalCase := ⟨3,185,.south,.push 211 (.stay 237),frame759⟩
theorem frame759_checked : CountedLocalCaseData.check data frame759 = true := by decide +kernel
theorem case759_fitted : fits case759 = true := by decide +kernel
noncomputable def frame760 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 17, changes := [(212, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832874, afterBeta := 5439691, afterBonus := 5832871, preBeta := 5439691, preBonus := 5834766, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1342998, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343002, updateProofs := some (76625, 378380), numericProof := 77171, slack := 0}
noncomputable def case760 : PhysicalCase := ⟨3,210,.east,.push 211 (.stay 212),frame760⟩
theorem frame760_checked : CountedLocalCaseData.check data frame760 = true := by decide +kernel
theorem case760_fitted : fits case760 = true := by decide +kernel
noncomputable def frame761 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 17, changes := [(210, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832870, afterBeta := 5439691, afterBonus := 5832871, preBeta := 5439691, preBonus := 5834769, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343006, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343009, updateProofs := some (77839, 378384), numericProof := 77172, slack := 2}
noncomputable def case761 : PhysicalCase := ⟨3,212,.west,.push 211 (.stay 210),frame761⟩
theorem frame761_checked : CountedLocalCaseData.check data frame761 = true := by decide +kernel
theorem case761_fitted : fits case761 = true := by decide +kernel
noncomputable def frame762 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 17, changes := [(186, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832875, afterBeta := 5439691, afterBonus := 5832870, preBeta := 5440955, preBonus := 5834771, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1343013, restrictionAfterBeta := 946126, restrictionAfterBonus := 1343016, updateProofs := some (78819, 378388), numericProof := 77173, slack := 0}
noncomputable def case762 : PhysicalCase := ⟨3,238,.north,.push 212 (.stay 186),frame762⟩
theorem frame762_checked : CountedLocalCaseData.check data frame762 = true := by decide +kernel
theorem case762_fitted : fits case762 = true := by decide +kernel
noncomputable def frame763 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 17, changes := [(238, true), (212, false)], beforeBeta := 5439697, beforeBonus := 5832864, afterBeta := 5439691, afterBonus := 5832870, preBeta := 5439691, preBonus := 5834773, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1343019, restrictionAfterBeta := 79701, restrictionAfterBonus := 1343022, updateProofs := some (79946, 378392), numericProof := 77174, slack := 2}
noncomputable def case763 : PhysicalCase := ⟨3,186,.south,.push 212 (.stay 238),frame763⟩
theorem frame763_checked : CountedLocalCaseData.check data frame763 = true := by decide +kernel
theorem case763_fitted : fits case763 = true := by decide +kernel
noncomputable def frame764 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 17, changes := [(213, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832871, afterBeta := 5439691, afterBonus := 5832870, preBeta := 5439691, preBonus := 5834776, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343026, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343030, updateProofs := some (80993, 378396), numericProof := 77175, slack := 2}
noncomputable def case764 : PhysicalCase := ⟨3,211,.east,.push 212 (.stay 213),frame764⟩
theorem frame764_checked : CountedLocalCaseData.check data frame764 = true := by decide +kernel
theorem case764_fitted : fits case764 = true := by decide +kernel
noncomputable def frame765 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 17, changes := [(211, true), (212, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832870, preBeta := 5439691, preBonus := 5834778, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343033, updateProofs := some (82020, 378400), numericProof := 77176, slack := 2}
noncomputable def case765 : PhysicalCase := ⟨3,213,.west,.push 212 (.stay 211),frame765⟩
theorem frame765_checked : CountedLocalCaseData.check data frame765 = true := by decide +kernel
theorem case765_fitted : fits case765 = true := by decide +kernel
noncomputable def frame766 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 17, changes := [(187, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832876, afterBeta := 5439691, afterBonus := 0, preBeta := 5441017, preBonus := 0, restrictionBeforeBeta := 98598, restrictionBeforeBonus := 1343037, restrictionAfterBeta := 1011364, restrictionAfterBonus := 3, updateProofs := some (83472, 82021), numericProof := 77177, slack := 2}
noncomputable def case766 : PhysicalCase := ⟨3,239,.north,.push 213 (.stay 187),frame766⟩
theorem frame766_checked : CountedLocalCaseData.check data frame766 = true := by decide +kernel
theorem case766_fitted : fits case766 = true := by decide +kernel
noncomputable def frame767 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 17, changes := [(239, true), (213, false)], beforeBeta := 5439698, beforeBonus := 5832865, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1343040, restrictionAfterBeta := 98598, restrictionAfterBonus := 3, updateProofs := some (85101, 83473), numericProof := 77178, slack := 2}
noncomputable def case767 : PhysicalCase := ⟨3,187,.south,.push 213 (.stay 239),frame767⟩
theorem frame767_checked : CountedLocalCaseData.check data frame767 = true := by decide +kernel
theorem case767_fitted : fits case767 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
