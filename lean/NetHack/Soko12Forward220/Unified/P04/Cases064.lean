import NetHack.Soko12Forward220.Unified.P04.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban
noncomputable def frame768 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 16, changes := [(187, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832904, afterBeta := 5439691, afterBonus := 0, preBeta := 5441017, preBonus := 0, restrictionBeforeBeta := 98598, restrictionBeforeBonus := 1344381, restrictionAfterBeta := 1011364, restrictionAfterBonus := 3, updateProofs := some (83472, 82021), numericProof := 77719, slack := 2}
noncomputable def case768 : PhysicalCase := ⟨4,239,.north,.push 213 (.stay 187),frame768⟩
theorem frame768_checked : CountedLocalCaseData.check data frame768 = true := by decide +kernel
theorem case768_fitted : fits case768 = true := by decide +kernel
noncomputable def frame769 : CountedLocalCase.Frame := {bindings := [(187, false), (213, true), (239, false)], budget := 16, changes := [(239, true), (213, false)], beforeBeta := 5439698, beforeBonus := 5832894, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 31129, restrictionBeforeBonus := 1344383, restrictionAfterBeta := 98598, restrictionAfterBonus := 3, updateProofs := some (85101, 83473), numericProof := 77720, slack := 2}
noncomputable def case769 : PhysicalCase := ⟨4,187,.south,.push 213 (.stay 239),frame769⟩
theorem frame769_checked : CountedLocalCaseData.check data frame769 = true := by decide +kernel
theorem case769_fitted : fits case769 = true := by decide +kernel
noncomputable def frame770 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 16, changes := [(214, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832897, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1344386, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (86561, 85102), numericProof := 77721, slack := 2}
noncomputable def case770 : PhysicalCase := ⟨4,212,.east,.push 213 (.stay 214),frame770⟩
theorem frame770_checked : CountedLocalCaseData.check data frame770 = true := by decide +kernel
theorem case770_fitted : fits case770 = true := by decide +kernel
noncomputable def frame771 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 16, changes := [(212, true), (213, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (88021, 86562), numericProof := 77722, slack := 0}
noncomputable def case771 : PhysicalCase := ⟨4,214,.west,.push 213 (.stay 212),frame771⟩
theorem frame771_checked : CountedLocalCaseData.check data frame771 = true := by decide +kernel
theorem case771_fitted : fits case771 = true := by decide +kernel
noncomputable def frame772 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 16, changes := [(215, true), (214, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (90209, 88022), numericProof := 77723, slack := 2}
noncomputable def case772 : PhysicalCase := ⟨4,213,.east,.push 214 (.stay 215),frame772⟩
theorem frame772_checked : CountedLocalCaseData.check data frame772 = true := by decide +kernel
theorem case772_fitted : fits case772 = true := by decide +kernel
noncomputable def frame773 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 16, changes := [(213, true), (214, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (92397, 90210), numericProof := 77724, slack := 0}
noncomputable def case773 : PhysicalCase := ⟨4,215,.west,.push 214 (.stay 213),frame773⟩
theorem frame773_checked : CountedLocalCaseData.check data frame773 = true := by decide +kernel
theorem case773_fitted : fits case773 = true := by decide +kernel
noncomputable def frame774 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 16, changes := [(189, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (94578, 92398), numericProof := 77725, slack := 2}
noncomputable def case774 : PhysicalCase := ⟨4,241,.north,.push 215 (.stay 189),frame774⟩
theorem frame774_checked : CountedLocalCaseData.check data frame774 = true := by decide +kernel
theorem case774_fitted : fits case774 = true := by decide +kernel
noncomputable def frame775 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 16, changes := [(241, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (97695, 94579), numericProof := 77726, slack := 8}
noncomputable def case775 : PhysicalCase := ⟨4,189,.south,.push 215 (.stay 241),frame775⟩
theorem frame775_checked : CountedLocalCaseData.check data frame775 = true := by decide +kernel
theorem case775_fitted : fits case775 = true := by decide +kernel
noncomputable def frame776 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 16, changes := [(216, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (100422, 97696), numericProof := 77727, slack := 4}
noncomputable def case776 : PhysicalCase := ⟨4,214,.east,.push 215 (.stay 216),frame776⟩
theorem frame776_checked : CountedLocalCaseData.check data frame776 = true := by decide +kernel
theorem case776_fitted : fits case776 = true := by decide +kernel
noncomputable def frame777 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 16, changes := [(214, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (103149, 100423), numericProof := 77728, slack := 0}
noncomputable def case777 : PhysicalCase := ⟨4,216,.west,.push 215 (.stay 214),frame777⟩
theorem frame777_checked : CountedLocalCaseData.check data frame777 = true := by decide +kernel
theorem case777_fitted : fits case777 = true := by decide +kernel
noncomputable def frame778 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 16, changes := [(190, true), (216, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (104544, 103150), numericProof := 77729, slack := 0}
noncomputable def case778 : PhysicalCase := ⟨4,242,.north,.push 216 (.stay 190),frame778⟩
theorem frame778_checked : CountedLocalCaseData.check data frame778 = true := by decide +kernel
theorem case778_fitted : fits case778 = true := by decide +kernel
noncomputable def frame779 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 16, changes := [(242, true), (216, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (107915, 104545), numericProof := 77730, slack := 5}
noncomputable def case779 : PhysicalCase := ⟨4,190,.south,.push 216 (.stay 242),frame779⟩
theorem frame779_checked : CountedLocalCaseData.check data frame779 = true := by decide +kernel
theorem case779_fitted : fits case779 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P04
