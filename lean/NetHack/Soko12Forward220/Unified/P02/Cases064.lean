import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame768 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 18, changes := [(215, true), (214, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (90209, 88022), numericProof := 76590, slack := 2}
noncomputable def case768 : PhysicalCase := ⟨2,213,.east,.push 214 (.stay 215),frame768⟩
theorem frame768_checked : CountedLocalCaseData.check data frame768 = true := by decide +kernel
theorem case768_fitted : fits case768 = true := by decide +kernel
noncomputable def frame769 : CountedLocalCase.Frame := {bindings := [(213, false), (214, true), (215, false)], budget := 18, changes := [(213, true), (214, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (92397, 90210), numericProof := 76591, slack := 0}
noncomputable def case769 : PhysicalCase := ⟨2,215,.west,.push 214 (.stay 213),frame769⟩
theorem frame769_checked : CountedLocalCaseData.check data frame769 = true := by decide +kernel
theorem case769_fitted : fits case769 = true := by decide +kernel
noncomputable def frame770 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 18, changes := [(189, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (94578, 92398), numericProof := 76592, slack := 2}
noncomputable def case770 : PhysicalCase := ⟨2,241,.north,.push 215 (.stay 189),frame770⟩
theorem frame770_checked : CountedLocalCaseData.check data frame770 = true := by decide +kernel
theorem case770_fitted : fits case770 = true := by decide +kernel
noncomputable def frame771 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 18, changes := [(241, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (97695, 94579), numericProof := 76593, slack := 8}
noncomputable def case771 : PhysicalCase := ⟨2,189,.south,.push 215 (.stay 241),frame771⟩
theorem frame771_checked : CountedLocalCaseData.check data frame771 = true := by decide +kernel
theorem case771_fitted : fits case771 = true := by decide +kernel
noncomputable def frame772 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 18, changes := [(216, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (100422, 97696), numericProof := 76594, slack := 4}
noncomputable def case772 : PhysicalCase := ⟨2,214,.east,.push 215 (.stay 216),frame772⟩
theorem frame772_checked : CountedLocalCaseData.check data frame772 = true := by decide +kernel
theorem case772_fitted : fits case772 = true := by decide +kernel
noncomputable def frame773 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 18, changes := [(214, true), (215, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (103149, 100423), numericProof := 76595, slack := 0}
noncomputable def case773 : PhysicalCase := ⟨2,216,.west,.push 215 (.stay 214),frame773⟩
theorem frame773_checked : CountedLocalCaseData.check data frame773 = true := by decide +kernel
theorem case773_fitted : fits case773 = true := by decide +kernel
noncomputable def frame774 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 18, changes := [(190, true), (216, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (104544, 103150), numericProof := 76596, slack := 0}
noncomputable def case774 : PhysicalCase := ⟨2,242,.north,.push 216 (.stay 190),frame774⟩
theorem frame774_checked : CountedLocalCaseData.check data frame774 = true := by decide +kernel
theorem case774_fitted : fits case774 = true := by decide +kernel
noncomputable def frame775 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 18, changes := [(242, true), (216, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (107915, 104545), numericProof := 76597, slack := 5}
noncomputable def case775 : PhysicalCase := ⟨2,190,.south,.push 216 (.stay 242),frame775⟩
theorem frame775_checked : CountedLocalCaseData.check data frame775 = true := by decide +kernel
theorem case775_fitted : fits case775 = true := by decide +kernel
noncomputable def frame776 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 18, changes := [(192, true), (218, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 3, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (110285, 107916), numericProof := 76598, slack := 0}
noncomputable def case776 : PhysicalCase := ⟨2,244,.north,.push 218 (.stay 192),frame776⟩
theorem frame776_checked : CountedLocalCaseData.check data frame776 = true := by decide +kernel
theorem case776_fitted : fits case776 = true := by decide +kernel
noncomputable def frame777 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 18, changes := [(244, true), (218, false)], beforeBeta := 5439699, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 3, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (113538, 110286), numericProof := 76599, slack := 2}
noncomputable def case777 : PhysicalCase := ⟨2,192,.south,.push 218 (.stay 244),frame777⟩
theorem frame777_checked : CountedLocalCaseData.check data frame777 = true := by decide +kernel
theorem case777_fitted : fits case777 = true := by decide +kernel
noncomputable def frame778 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 18, changes := [(193, true), (219, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5440866, preBonus := 0, restrictionBeforeBeta := 51655, restrictionBeforeBonus := 3, restrictionAfterBeta := 1051124, restrictionAfterBonus := 3, updateProofs := some (116890, 113539), numericProof := 76600, slack := 0}
noncomputable def case778 : PhysicalCase := ⟨2,245,.north,.push 219 (.stay 193),frame778⟩
theorem frame778_checked : CountedLocalCaseData.check data frame778 = true := by decide +kernel
theorem case778_fitted : fits case778 = true := by decide +kernel
noncomputable def frame779 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 18, changes := [(245, true), (219, false)], beforeBeta := 5439700, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 52977, restrictionBeforeBonus := 3, restrictionAfterBeta := 51655, restrictionAfterBonus := 3, updateProofs := some (121217, 116891), numericProof := 76601, slack := 2}
noncomputable def case779 : PhysicalCase := ⟨2,193,.south,.push 219 (.stay 245),frame779⟩
theorem frame779_checked : CountedLocalCaseData.check data frame779 = true := by decide +kernel
theorem case779_fitted : fits case779 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
