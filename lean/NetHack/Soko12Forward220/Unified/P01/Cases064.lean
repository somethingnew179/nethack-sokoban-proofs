import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame768 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 19, changes := [(189, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832785, preBeta := 5439691, preBonus := 5834023, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337496, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337498, updateProofs := some (94578, 376429), numericProof := 75769, slack := 2}
noncomputable def case768 : PhysicalCase := ⟨1,241,.north,.push 215 (.stay 189),frame768⟩
theorem frame768_checked : CountedLocalCaseData.check data frame768 = true := by decide +kernel
theorem case768_fitted : fits case768 = true := by decide +kernel
noncomputable def frame769 : CountedLocalCase.Frame := {bindings := [(189, false), (215, true), (241, false)], budget := 19, changes := [(241, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832793, afterBeta := 5439691, afterBonus := 5832785, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337500, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (97695, 376431), numericProof := 75770, slack := 8}
noncomputable def case769 : PhysicalCase := ⟨1,189,.south,.push 215 (.stay 241),frame769⟩
theorem frame769_checked : CountedLocalCaseData.check data frame769 = true := by decide +kernel
theorem case769_fitted : fits case769 = true := by decide +kernel
noncomputable def frame770 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 19, changes := [(216, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832783, afterBeta := 5439691, afterBonus := 5832785, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337502, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (100422, 376433), numericProof := 75771, slack := 4}
noncomputable def case770 : PhysicalCase := ⟨1,214,.east,.push 215 (.stay 216),frame770⟩
theorem frame770_checked : CountedLocalCaseData.check data frame770 = true := by decide +kernel
theorem case770_fitted : fits case770 = true := by decide +kernel
noncomputable def frame771 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 19, changes := [(214, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832785, preBeta := 5439691, preBonus := 5834086, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337504, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337506, updateProofs := some (103149, 376435), numericProof := 75772, slack := 0}
noncomputable def case771 : PhysicalCase := ⟨1,216,.west,.push 215 (.stay 214),frame771⟩
theorem frame771_checked : CountedLocalCaseData.check data frame771 = true := by decide +kernel
theorem case771_fitted : fits case771 = true := by decide +kernel
noncomputable def frame772 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 19, changes := [(190, true), (216, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832786, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337508, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (104544, 376437), numericProof := 75773, slack := 0}
noncomputable def case772 : PhysicalCase := ⟨1,242,.north,.push 216 (.stay 190),frame772⟩
theorem frame772_checked : CountedLocalCaseData.check data frame772 = true := by decide +kernel
theorem case772_fitted : fits case772 = true := by decide +kernel
noncomputable def frame773 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 19, changes := [(242, true), (216, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832786, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337508, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (107915, 376439), numericProof := 75774, slack := 5}
noncomputable def case773 : PhysicalCase := ⟨1,190,.south,.push 216 (.stay 242),frame773⟩
theorem frame773_checked : CountedLocalCaseData.check data frame773 = true := by decide +kernel
theorem case773_fitted : fits case773 = true := by decide +kernel
noncomputable def frame774 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 19, changes := [(192, true), (218, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832811, preBeta := 5440852, preBonus := 5834088, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 1337510, restrictionAfterBeta := 935300, restrictionAfterBonus := 1337512, updateProofs := some (110285, 376441), numericProof := 75778, slack := 0}
noncomputable def case774 : PhysicalCase := ⟨1,244,.north,.push 218 (.stay 192),frame774⟩
theorem frame774_checked : CountedLocalCaseData.check data frame774 = true := by decide +kernel
theorem case774_fitted : fits case774 = true := by decide +kernel
noncomputable def frame775 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 19, changes := [(244, true), (218, false)], beforeBeta := 5439699, beforeBonus := 5832791, afterBeta := 5439691, afterBonus := 5832811, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 1337514, restrictionAfterBeta := 44389, restrictionAfterBonus := 3, updateProofs := some (113538, 376443), numericProof := 75779, slack := 2}
noncomputable def case775 : PhysicalCase := ⟨1,192,.south,.push 218 (.stay 244),frame775⟩
theorem frame775_checked : CountedLocalCaseData.check data frame775 = true := by decide +kernel
theorem case775_fitted : fits case775 = true := by decide +kernel
noncomputable def frame776 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 19, changes := [(193, true), (219, false)], beforeBeta := 5439691, beforeBonus := 5832806, afterBeta := 5439691, afterBonus := 5832799, preBeta := 5440866, preBonus := 5834092, restrictionBeforeBeta := 51655, restrictionBeforeBonus := 1337516, restrictionAfterBeta := 1051124, restrictionAfterBonus := 1337518, updateProofs := some (116890, 376445), numericProof := 75783, slack := 0}
noncomputable def case776 : PhysicalCase := ⟨1,245,.north,.push 219 (.stay 193),frame776⟩
theorem frame776_checked : CountedLocalCaseData.check data frame776 = true := by decide +kernel
theorem case776_fitted : fits case776 = true := by decide +kernel
noncomputable def frame777 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 19, changes := [(245, true), (219, false)], beforeBeta := 5439700, beforeBonus := 5832797, afterBeta := 5439691, afterBonus := 5832799, preBeta := 5439691, preBonus := 5834095, restrictionBeforeBeta := 52977, restrictionBeforeBonus := 1337520, restrictionAfterBeta := 51655, restrictionAfterBonus := 1337522, updateProofs := some (121217, 376447), numericProof := 75784, slack := 2}
noncomputable def case777 : PhysicalCase := ⟨1,193,.south,.push 219 (.stay 245),frame777⟩
theorem frame777_checked : CountedLocalCaseData.check data frame777 = true := by decide +kernel
theorem case777_fitted : fits case777 = true := by decide +kernel
noncomputable def frame778 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 19, changes := [(220, true), (219, false)], beforeBeta := 5439691, beforeBonus := 5832811, afterBeta := 5439691, afterBonus := 5832799, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337524, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (125145, 376449), numericProof := 75785, slack := 2}
noncomputable def case778 : PhysicalCase := ⟨1,218,.east,.push 219 (.stay 220),frame778⟩
theorem frame778_checked : CountedLocalCaseData.check data frame778 = true := by decide +kernel
theorem case778_fitted : fits case778 = true := by decide +kernel
noncomputable def frame779 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 19, changes := [(218, true), (219, false)], beforeBeta := 5439691, beforeBonus := 5832804, afterBeta := 5439691, afterBonus := 5832799, preBeta := 5439691, preBonus := 5834099, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337526, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337528, updateProofs := some (129041, 376451), numericProof := 75789, slack := 0}
noncomputable def case779 : PhysicalCase := ⟨1,220,.west,.push 219 (.stay 218),frame779⟩
theorem frame779_checked : CountedLocalCaseData.check data frame779 = true := by decide +kernel
theorem case779_fitted : fits case779 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
