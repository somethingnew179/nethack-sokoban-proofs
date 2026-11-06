import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame792 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 16, changes := [(238, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832901, afterBeta := 5439691, afterBonus := 5832900, preBeta := 5439691, preBonus := 5835063, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344405, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344408, updateProofs := some (144294, 378773), numericProof := 77745, slack := 0}
noncomputable def case792 : PhysicalCase := ⟨4,236,.east,.push 237 (.stay 238),frame792⟩
theorem frame792_checked : CountedLocalCaseData.check data frame792 = true := by decide +kernel
theorem case792_fitted : fits case792 = true := by decide +kernel
noncomputable def frame793 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 16, changes := [(236, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832903, afterBeta := 5439691, afterBonus := 5832900, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344411, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (145671, 378776), numericProof := 77746, slack := 2}
noncomputable def case793 : PhysicalCase := ⟨4,238,.west,.push 237 (.stay 236),frame793⟩
theorem frame793_checked : CountedLocalCaseData.check data frame793 = true := by decide +kernel
theorem case793_fitted : fits case793 = true := by decide +kernel
noncomputable def frame794 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 16, changes := [(212, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832905, afterBeta := 5439691, afterBonus := 5832903, preBeta := 5439691, preBonus := 5835066, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344414, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344416, updateProofs := some (146345, 378779), numericProof := 77747, slack := 0}
noncomputable def case794 : PhysicalCase := ⟨4,264,.north,.push 238 (.stay 212),frame794⟩
theorem frame794_checked : CountedLocalCaseData.check data frame794 = true := by decide +kernel
theorem case794_fitted : fits case794 = true := by decide +kernel
noncomputable def frame795 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 16, changes := [(264, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832897, afterBeta := 5439691, afterBonus := 5832903, preBeta := 5439691, preBonus := 5835068, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344419, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344421, updateProofs := some (147122, 378782), numericProof := 77748, slack := 2}
noncomputable def case795 : PhysicalCase := ⟨4,212,.south,.push 238 (.stay 264),frame795⟩
theorem frame795_checked : CountedLocalCaseData.check data frame795 = true := by decide +kernel
theorem case795_fitted : fits case795 = true := by decide +kernel
noncomputable def frame796 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 16, changes := [(239, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832900, afterBeta := 5439691, afterBonus := 5832903, preBeta := 5439691, preBonus := 5835070, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344424, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344427, updateProofs := some (147813, 378785), numericProof := 77749, slack := 2}
noncomputable def case796 : PhysicalCase := ⟨4,237,.east,.push 238 (.stay 239),frame796⟩
theorem frame796_checked : CountedLocalCaseData.check data frame796 = true := by decide +kernel
theorem case796_fitted : fits case796 = true := by decide +kernel
noncomputable def frame797 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 16, changes := [(237, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832904, afterBeta := 5439691, afterBonus := 5832903, preBeta := 5439691, preBonus := 5835073, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344430, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344432, updateProofs := some (148494, 378788), numericProof := 77750, slack := 2}
noncomputable def case797 : PhysicalCase := ⟨4,239,.west,.push 238 (.stay 237),frame797⟩
theorem frame797_checked : CountedLocalCaseData.check data frame797 = true := by decide +kernel
theorem case797_fitted : fits case797 = true := by decide +kernel
noncomputable def frame798 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 16, changes := [(213, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832906, afterBeta := 5439691, afterBonus := 5832904, preBeta := 5439691, preBonus := 5835075, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344435, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344438, updateProofs := some (150523, 378791), numericProof := 77751, slack := 0}
noncomputable def case798 : PhysicalCase := ⟨4,265,.north,.push 239 (.stay 213),frame798⟩
theorem frame798_checked : CountedLocalCaseData.check data frame798 = true := by decide +kernel
theorem case798_fitted : fits case798 = true := by decide +kernel
noncomputable def frame799 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 16, changes := [(265, true), (239, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832904, preBeta := 5439691, preBonus := 5835076, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1344441, updateProofs := some (152932, 378794), numericProof := 77752, slack := 2}
noncomputable def case799 : PhysicalCase := ⟨4,213,.south,.push 239 (.stay 265),frame799⟩
theorem frame799_checked : CountedLocalCaseData.check data frame799 = true := by decide +kernel
theorem case799_fitted : fits case799 = true := by decide +kernel
noncomputable def frame800 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 16, changes := [(218, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (157267, 152933), numericProof := 77753, slack := 0}
noncomputable def case800 : PhysicalCase := ⟨4,270,.north,.push 244 (.stay 218),frame800⟩
theorem frame800_checked : CountedLocalCaseData.check data frame800 = true := by decide +kernel
theorem case800_fitted : fits case800 = true := by decide +kernel
noncomputable def frame801 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 16, changes := [(270, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (161757, 157268), numericProof := 77754, slack := 2}
noncomputable def case801 : PhysicalCase := ⟨4,218,.south,.push 244 (.stay 270),frame801⟩
theorem frame801_checked : CountedLocalCaseData.check data frame801 = true := by decide +kernel
theorem case801_fitted : fits case801 = true := by decide +kernel
noncomputable def frame802 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 16, changes := [(219, true), (245, false)], beforeBeta := 5439701, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 426739, restrictionBeforeBonus := 3, restrictionAfterBeta := 422199, restrictionAfterBonus := 3, updateProofs := some (166105, 161758), numericProof := 77755, slack := 0}
noncomputable def case802 : PhysicalCase := ⟨4,271,.north,.push 245 (.stay 219),frame802⟩
theorem frame802_checked : CountedLocalCaseData.check data frame802 = true := by decide +kernel
theorem case802_fitted : fits case802 = true := by decide +kernel
noncomputable def frame803 : CountedLocalCase.Frame := {bindings := [(219, false), (245, true), (271, false)], budget := 16, changes := [(271, true), (245, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5441377, preBonus := 0, restrictionBeforeBeta := 422199, restrictionBeforeBonus := 3, restrictionAfterBeta := 1116377, restrictionAfterBonus := 3, updateProofs := some (170833, 166106), numericProof := 77756, slack := 1}
noncomputable def case803 : PhysicalCase := ⟨4,219,.south,.push 245 (.stay 271),frame803⟩
theorem frame803_checked : CountedLocalCaseData.check data frame803 = true := by decide +kernel
theorem case803_fitted : fits case803 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
