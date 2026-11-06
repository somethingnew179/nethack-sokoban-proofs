import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame768 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 17, changes := [(214, true), (213, false)], beforeBeta := 5439691, beforeBonus := 5832870, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343044, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (86561, 85102), numericProof := 77179, slack := 2}
noncomputable def case768 : PhysicalCase := ⟨3,212,.east,.push 213 (.stay 214),frame768⟩
theorem frame768_checked : CountedLocalCaseData.check data frame768 = true := by decide +kernel
theorem case768_fitted : fits case768 = true := by decide +kernel
noncomputable def frame769 : CountedLocalCase.Frame := {bindings := [(212, false), (213, true), (214, false)], budget := 17, changes := [(212, true), (213, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (88021, 86562), numericProof := 77180, slack := 0}
noncomputable def case769 : PhysicalCase := ⟨3,214,.west,.push 213 (.stay 212),frame769⟩
theorem frame769_checked : CountedLocalCaseData.check data frame769 = true := by decide +kernel
theorem case769_fitted : fits case769 = true := by decide +kernel
noncomputable def frame770 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 17, changes := [(215, true), (214, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (90209, 88022), numericProof := 77181, slack := 2}
noncomputable def case770 : PhysicalCase := ⟨3,213,.east,.push 214 (.stay 215),frame770⟩
theorem frame770_checked : CountedLocalCaseData.check data frame770 = true := by decide +kernel
theorem case770_fitted : fits case770 = true := by decide +kernel
noncomputable def frame771 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 17, changes := [(213, true), (214, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (92397, 90210), numericProof := 77182, slack := 0}
noncomputable def case771 : PhysicalCase := ⟨3,215,.west,.push 214 (.stay 213),frame771⟩
theorem frame771_checked : CountedLocalCaseData.check data frame771 = true := by decide +kernel
theorem case771_fitted : fits case771 = true := by decide +kernel
noncomputable def frame772 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 17, changes := [(189, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (94578, 92398), numericProof := 77183, slack := 2}
noncomputable def case772 : PhysicalCase := ⟨3,241,.north,.push 215 (.stay 189),frame772⟩
theorem frame772_checked : CountedLocalCaseData.check data frame772 = true := by decide +kernel
theorem case772_fitted : fits case772 = true := by decide +kernel
noncomputable def frame773 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 17, changes := [(241, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (97695, 94579), numericProof := 77184, slack := 8}
noncomputable def case773 : PhysicalCase := ⟨3,189,.south,.push 215 (.stay 241),frame773⟩
theorem frame773_checked : CountedLocalCaseData.check data frame773 = true := by decide +kernel
theorem case773_fitted : fits case773 = true := by decide +kernel
noncomputable def frame774 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 17, changes := [(216, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (100422, 97696), numericProof := 77185, slack := 4}
noncomputable def case774 : PhysicalCase := ⟨3,214,.east,.push 215 (.stay 216),frame774⟩
theorem frame774_checked : CountedLocalCaseData.check data frame774 = true := by decide +kernel
theorem case774_fitted : fits case774 = true := by decide +kernel
noncomputable def frame775 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 17, changes := [(214, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (103149, 100423), numericProof := 77186, slack := 0}
noncomputable def case775 : PhysicalCase := ⟨3,216,.west,.push 215 (.stay 214),frame775⟩
theorem frame775_checked : CountedLocalCaseData.check data frame775 = true := by decide +kernel
theorem case775_fitted : fits case775 = true := by decide +kernel
noncomputable def frame776 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 17, changes := [(190, true), (216, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (104544, 103150), numericProof := 77187, slack := 0}
noncomputable def case776 : PhysicalCase := ⟨3,242,.north,.push 216 (.stay 190),frame776⟩
theorem frame776_checked : CountedLocalCaseData.check data frame776 = true := by decide +kernel
theorem case776_fitted : fits case776 = true := by decide +kernel
noncomputable def frame777 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 17, changes := [(242, true), (216, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (107915, 104545), numericProof := 77188, slack := 5}
noncomputable def case777 : PhysicalCase := ⟨3,190,.south,.push 216 (.stay 242),frame777⟩
theorem frame777_checked : CountedLocalCaseData.check data frame777 = true := by decide +kernel
theorem case777_fitted : fits case777 = true := by decide +kernel
noncomputable def frame778 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 17, changes := [(192, true), (218, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (110285, 107916), numericProof := 77189, slack := 0}
noncomputable def case778 : PhysicalCase := ⟨3,244,.north,.push 218 (.stay 192),frame778⟩
theorem frame778_checked : CountedLocalCaseData.check data frame778 = true := by decide +kernel
theorem case778_fitted : fits case778 = true := by decide +kernel
noncomputable def frame779 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 17, changes := [(244, true), (218, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (113538, 110286), numericProof := 77190, slack := 2}
noncomputable def case779 : PhysicalCase := ⟨3,192,.south,.push 218 (.stay 244),frame779⟩
theorem frame779_checked : CountedLocalCaseData.check data frame779 = true := by decide +kernel
theorem case779_fitted : fits case779 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
