import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame756 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 19, changes := [(212, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832796, afterBeta := 5439691, afterBonus := 5832794, preBeta := 5439691, preBonus := 5834061, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337329, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337348, updateProofs := some (76625, 376338), numericProof := 75753, slack := 0}
noncomputable def case756 : PhysicalCase := ⟨1,210,.east,.push 211 (.stay 212),frame756⟩
theorem frame756_checked : CountedLocalCaseData.check data frame756 = true := by decide +kernel
theorem case756_fitted : fits case756 = true := by decide +kernel
noncomputable def frame757 : CountedLocalCase.Frame := {bindings := [(210, false), (211, true), (212, false)], budget := 19, changes := [(210, true), (211, false)], beforeBeta := 5439691, beforeBonus := 5832789, afterBeta := 5439691, afterBonus := 5832794, preBeta := 5439691, preBonus := 5834064, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337361, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337368, updateProofs := some (77839, 376359), numericProof := 75754, slack := 2}
noncomputable def case757 : PhysicalCase := ⟨1,212,.west,.push 211 (.stay 210),frame757⟩
theorem frame757_checked : CountedLocalCaseData.check data frame757 = true := by decide +kernel
theorem case757_fitted : fits case757 = true := by decide +kernel
noncomputable def frame758 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 19, changes := [(186, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832818, afterBeta := 5439691, afterBonus := 5832789, preBeta := 5440955, preBonus := 5834066, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1337382, restrictionAfterBeta := 946126, restrictionAfterBonus := 1337389, updateProofs := some (78819, 376373), numericProof := 75759, slack := 0}
noncomputable def case758 : PhysicalCase := ⟨1,238,.north,.push 212 (.stay 186),frame758⟩
theorem frame758_checked : CountedLocalCaseData.check data frame758 = true := by decide +kernel
theorem case758_fitted : fits case758 = true := by decide +kernel
noncomputable def frame759 : CountedLocalCase.Frame := {bindings := [(186, false), (212, true), (238, false)], budget := 19, changes := [(238, true), (212, false)], beforeBeta := 5439697, beforeBonus := 5832780, afterBeta := 5439691, afterBonus := 5832789, preBeta := 5439691, preBonus := 5834069, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1337396, restrictionAfterBeta := 79701, restrictionAfterBonus := 1337403, updateProofs := some (79946, 376387), numericProof := 75760, slack := 2}
noncomputable def case759 : PhysicalCase := ⟨1,186,.south,.push 212 (.stay 238),frame759⟩
theorem frame759_checked : CountedLocalCaseData.check data frame759 = true := by decide +kernel
theorem case759_fitted : fits case759 = true := by decide +kernel
noncomputable def frame760 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 19, changes := [(213, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832794, afterBeta := 5439691, afterBonus := 5832789, preBeta := 5439691, preBonus := 5834072, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337424, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337438, updateProofs := some (80993, 376401), numericProof := 75761, slack := 2}
noncomputable def case760 : PhysicalCase := ⟨1,211,.east,.push 212 (.stay 213),frame760⟩
theorem frame760_checked : CountedLocalCaseData.check data frame760 = true := by decide +kernel
theorem case760_fitted : fits case760 = true := by decide +kernel
noncomputable def frame761 : CountedLocalCase.Frame := {bindings := [(211, false), (212, true), (213, false)], budget := 19, changes := [(211, true), (212, false)], beforeBeta := 5439691, beforeBonus := 5832782, afterBeta := 5439691, afterBonus := 5832789, preBeta := 5439691, preBonus := 5834075, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337440, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337447, updateProofs := some (82020, 376415), numericProof := 75762, slack := 2}
noncomputable def case761 : PhysicalCase := ⟨1,213,.west,.push 212 (.stay 211),frame761⟩
theorem frame761_checked : CountedLocalCaseData.check data frame761 = true := by decide +kernel
theorem case761_fitted : fits case761 = true := by decide +kernel
noncomputable def frame762 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 19, changes := [(187, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832784, afterBeta := 5439691, afterBonus := 5832782, preBeta := 5441017, preBonus := 5834077, restrictionBeforeBeta := 98598, restrictionBeforeBonus := 1337461, restrictionAfterBeta := 1011364, restrictionAfterBonus := 1337463, updateProofs := some (83472, 376417), numericProof := 75763, slack := 2}
noncomputable def case762 : PhysicalCase := ⟨1,239,.north,.push 213 (.stay 187),frame762⟩
theorem frame762_checked : CountedLocalCaseData.check data frame762 = true := by decide +kernel
theorem case762_fitted : fits case762 = true := by decide +kernel
noncomputable def frame763 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 19, changes := [(239, true), (213, false)], beforeBeta := 5439698, beforeBonus := 5832781, afterBeta := 5439691, afterBonus := 5832782, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1337470, restrictionAfterBeta := 98598, restrictionAfterBonus := 3, updateProofs := some (85101, 376419), numericProof := 75764, slack := 2}
noncomputable def case763 : PhysicalCase := ⟨1,187,.south,.push 213 (.stay 239),frame763⟩
theorem frame763_checked : CountedLocalCaseData.check data frame763 = true := by decide +kernel
theorem case763_fitted : fits case763 = true := by decide +kernel
noncomputable def frame764 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 19, changes := [(214, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832789, afterBeta := 5439691, afterBonus := 5832782, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337484, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (86561, 376421), numericProof := 75765, slack := 2}
noncomputable def case764 : PhysicalCase := ⟨1,212,.east,.push 213 (.stay 214),frame764⟩
theorem frame764_checked : CountedLocalCaseData.check data frame764 = true := by decide +kernel
theorem case764_fitted : fits case764 = true := by decide +kernel
noncomputable def frame765 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 19, changes := [(212, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832783, afterBeta := 5439691, afterBonus := 5832782, preBeta := 5439691, preBonus := 5834081, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337486, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337488, updateProofs := some (88021, 376423), numericProof := 75766, slack := 0}
noncomputable def case765 : PhysicalCase := ⟨1,214,.west,.push 213 (.stay 212),frame765⟩
theorem frame765_checked : CountedLocalCaseData.check data frame765 = true := by decide +kernel
theorem case765_fitted : fits case765 = true := by decide +kernel
noncomputable def frame766 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 19, changes := [(215, true), (214, false)], beforeBeta := 5439691, beforeBonus := 5832782, afterBeta := 5439691, afterBonus := 5832783, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337490, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (90209, 376425), numericProof := 75767, slack := 2}
noncomputable def case766 : PhysicalCase := ⟨1,213,.east,.push 214 (.stay 215),frame766⟩
theorem frame766_checked : CountedLocalCaseData.check data frame766 = true := by decide +kernel
theorem case766_fitted : fits case766 = true := by decide +kernel
noncomputable def frame767 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 19, changes := [(213, true), (214, false)], beforeBeta := 5439691, beforeBonus := 5832785, afterBeta := 5439691, afterBonus := 5832783, preBeta := 5439691, preBonus := 5834083, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337492, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337494, updateProofs := some (92397, 376427), numericProof := 75768, slack := 0}
noncomputable def case767 : PhysicalCase := ⟨1,215,.west,.push 214 (.stay 213),frame767⟩
theorem frame767_checked : CountedLocalCaseData.check data frame767 = true := by decide +kernel
theorem case767_fitted : fits case767 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
