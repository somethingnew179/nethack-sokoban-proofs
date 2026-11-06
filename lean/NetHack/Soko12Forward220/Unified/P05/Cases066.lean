import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame792 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 15, changes := [(211, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345146, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (141440, 379013), numericProof := 78257, slack := 0}
noncomputable def case792 : PhysicalCase := ⟨5,263,.north,.push 237 (.stay 211),frame792⟩
theorem frame792_checked : CountedLocalCaseData.check data frame792 = true := by decide +kernel
theorem case792_fitted : fits case792 = true := by decide +kernel
noncomputable def frame793 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 15, changes := [(263, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345146, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (142896, 379015), numericProof := 78258, slack := 2}
noncomputable def case793 : PhysicalCase := ⟨5,211,.south,.push 237 (.stay 263),frame793⟩
theorem frame793_checked : CountedLocalCaseData.check data frame793 = true := by decide +kernel
theorem case793_fitted : fits case793 = true := by decide +kernel
noncomputable def frame794 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 15, changes := [(238, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 5835253, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345148, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345150, updateProofs := some (144294, 379017), numericProof := 78259, slack := 0}
noncomputable def case794 : PhysicalCase := ⟨5,236,.east,.push 237 (.stay 238),frame794⟩
theorem frame794_checked : CountedLocalCaseData.check data frame794 = true := by decide +kernel
theorem case794_fitted : fits case794 = true := by decide +kernel
noncomputable def frame795 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 15, changes := [(236, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832911, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345152, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (145671, 379019), numericProof := 78260, slack := 2}
noncomputable def case795 : PhysicalCase := ⟨5,238,.west,.push 237 (.stay 236),frame795⟩
theorem frame795_checked : CountedLocalCaseData.check data frame795 = true := by decide +kernel
theorem case795_fitted : fits case795 = true := by decide +kernel
noncomputable def frame796 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 15, changes := [(212, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832911, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345154, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (146345, 379021), numericProof := 78261, slack := 0}
noncomputable def case796 : PhysicalCase := ⟨5,264,.north,.push 238 (.stay 212),frame796⟩
theorem frame796_checked : CountedLocalCaseData.check data frame796 = true := by decide +kernel
theorem case796_fitted : fits case796 = true := by decide +kernel
noncomputable def frame797 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 15, changes := [(264, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832911, afterBeta := 5439691, afterBonus := 5832911, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345156, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (147122, 379023), numericProof := 78262, slack := 2}
noncomputable def case797 : PhysicalCase := ⟨5,212,.south,.push 238 (.stay 264),frame797⟩
theorem frame797_checked : CountedLocalCaseData.check data frame797 = true := by decide +kernel
theorem case797_fitted : fits case797 = true := by decide +kernel
noncomputable def frame798 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 15, changes := [(239, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832911, preBeta := 5439691, preBonus := 5835255, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345158, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345160, updateProofs := some (147813, 379025), numericProof := 78263, slack := 2}
noncomputable def case798 : PhysicalCase := ⟨5,237,.east,.push 238 (.stay 239),frame798⟩
theorem frame798_checked : CountedLocalCaseData.check data frame798 = true := by decide +kernel
theorem case798_fitted : fits case798 = true := by decide +kernel
noncomputable def frame799 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 15, changes := [(237, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832912, afterBeta := 5439691, afterBonus := 5832911, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345162, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (148494, 379027), numericProof := 78264, slack := 2}
noncomputable def case799 : PhysicalCase := ⟨5,239,.west,.push 238 (.stay 237),frame799⟩
theorem frame799_checked : CountedLocalCaseData.check data frame799 = true := by decide +kernel
theorem case799_fitted : fits case799 = true := by decide +kernel
noncomputable def frame800 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 15, changes := [(213, true), (239, false)], beforeBeta := 5439691, beforeBonus := 5832913, afterBeta := 5439691, afterBonus := 5832912, preBeta := 5439691, preBonus := 5835258, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345164, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345166, updateProofs := some (150523, 379029), numericProof := 78265, slack := 0}
noncomputable def case800 : PhysicalCase := ⟨5,265,.north,.push 239 (.stay 213),frame800⟩
theorem frame800_checked : CountedLocalCaseData.check data frame800 = true := by decide +kernel
theorem case800_fitted : fits case800 = true := by decide +kernel
noncomputable def frame801 : CountedLocalCase.Frame := {bindings := [(213, false), (239, true), (265, false)], budget := 15, changes := [(265, true), (239, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832912, preBeta := 5439691, preBonus := 5835259, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345168, updateProofs := some (152932, 379031), numericProof := 78266, slack := 2}
noncomputable def case801 : PhysicalCase := ⟨5,213,.south,.push 239 (.stay 265),frame801⟩
theorem frame801_checked : CountedLocalCaseData.check data frame801 = true := by decide +kernel
theorem case801_fitted : fits case801 = true := by decide +kernel
noncomputable def frame802 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 15, changes := [(218, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (157267, 152933), numericProof := 78267, slack := 0}
noncomputable def case802 : PhysicalCase := ⟨5,270,.north,.push 244 (.stay 218),frame802⟩
theorem frame802_checked : CountedLocalCaseData.check data frame802 = true := by decide +kernel
theorem case802_fitted : fits case802 = true := by decide +kernel
noncomputable def frame803 : CountedLocalCase.Frame := {bindings := [(218, false), (244, true), (270, false)], budget := 15, changes := [(270, true), (244, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (161757, 157268), numericProof := 78268, slack := 2}
noncomputable def case803 : PhysicalCase := ⟨5,218,.south,.push 244 (.stay 270),frame803⟩
theorem frame803_checked : CountedLocalCaseData.check data frame803 = true := by decide +kernel
theorem case803_fitted : fits case803 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
