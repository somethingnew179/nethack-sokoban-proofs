import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame768 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 20, changes := [(216, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832737, afterBeta := 5439691, afterBonus := 5832734, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1030436, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (100422, 100348), numericProof := 47550, slack := 4}
noncomputable def case768 : PhysicalCase := ⟨0,214,.east,.push 215 (.stay 216),frame768⟩
theorem frame768_checked : CountedLocalCaseData.check data frame768 = true := by decide +kernel
theorem case768_fitted : fits case768 = true := by decide +kernel
noncomputable def frame769 : CountedLocalCase.Frame := {bindings := [(214, false), (215, true), (216, false)], budget := 20, changes := [(214, true), (215, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832734, preBeta := 5439691, preBonus := 5833472, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1033144, restrictionAfterBeta := 8531, restrictionAfterBonus := 1035371, updateProofs := some (103149, 103075), numericProof := 47551, slack := 0}
noncomputable def case769 : PhysicalCase := ⟨0,216,.west,.push 215 (.stay 214),frame769⟩
theorem frame769_checked : CountedLocalCaseData.check data frame769 = true := by decide +kernel
theorem case769_fitted : fits case769 = true := by decide +kernel
noncomputable def frame770 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 20, changes := [(190, true), (216, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832730, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1038232, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (104544, 104470), numericProof := 47552, slack := 0}
noncomputable def case770 : PhysicalCase := ⟨0,242,.north,.push 216 (.stay 190),frame770⟩
theorem frame770_checked : CountedLocalCaseData.check data frame770 = true := by decide +kernel
theorem case770_fitted : fits case770 = true := by decide +kernel
noncomputable def frame771 : CountedLocalCase.Frame := {bindings := [(190, false), (216, true), (242, false)], budget := 20, changes := [(242, true), (216, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832730, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1038232, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (107915, 107841), numericProof := 47553, slack := 5}
noncomputable def case771 : PhysicalCase := ⟨0,190,.south,.push 216 (.stay 242),frame771⟩
theorem frame771_checked : CountedLocalCaseData.check data frame771 = true := by decide +kernel
theorem case771_fitted : fits case771 = true := by decide +kernel
noncomputable def frame772 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 20, changes := [(192, true), (218, false)], beforeBeta := 5439691, beforeBonus := 5832714, afterBeta := 5439691, afterBonus := 5832728, preBeta := 5440852, preBonus := 5833474, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 1041908, restrictionAfterBeta := 935300, restrictionAfterBonus := 1043775, updateProofs := some (110285, 110211), numericProof := 49862, slack := 0}
noncomputable def case772 : PhysicalCase := ⟨0,244,.north,.push 218 (.stay 192),frame772⟩
theorem frame772_checked : CountedLocalCaseData.check data frame772 = true := by decide +kernel
theorem case772_fitted : fits case772 = true := by decide +kernel
noncomputable def frame773 : CountedLocalCase.Frame := {bindings := [(192, false), (218, true), (244, false)], budget := 20, changes := [(244, true), (218, false)], beforeBeta := 5439699, beforeBonus := 5832721, afterBeta := 5439691, afterBonus := 5832728, preBeta := 5439691, preBonus := 5833477, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 1047130, restrictionAfterBeta := 44389, restrictionAfterBonus := 1047465, updateProofs := some (113538, 113464), numericProof := 50711, slack := 2}
noncomputable def case773 : PhysicalCase := ⟨0,192,.south,.push 218 (.stay 244),frame773⟩
theorem frame773_checked : CountedLocalCaseData.check data frame773 = true := by decide +kernel
theorem case773_fitted : fits case773 = true := by decide +kernel
noncomputable def frame774 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 20, changes := [(193, true), (219, false)], beforeBeta := 5439691, beforeBonus := 5832715, afterBeta := 5439691, afterBonus := 5832717, preBeta := 5440866, preBonus := 5833480, restrictionBeforeBeta := 51655, restrictionBeforeBonus := 1051123, restrictionAfterBeta := 1051124, restrictionAfterBonus := 1053529, updateProofs := some (116890, 116816), numericProof := 53081, slack := 0}
noncomputable def case774 : PhysicalCase := ⟨0,245,.north,.push 219 (.stay 193),frame774⟩
theorem frame774_checked : CountedLocalCaseData.check data frame774 = true := by decide +kernel
theorem case774_fitted : fits case774 = true := by decide +kernel
noncomputable def frame775 : CountedLocalCase.Frame := {bindings := [(193, false), (219, true), (245, false)], budget := 20, changes := [(245, true), (219, false)], beforeBeta := 5439700, beforeBonus := 5832719, afterBeta := 5439691, afterBonus := 5832717, preBeta := 5439691, preBonus := 5833483, restrictionBeforeBeta := 52977, restrictionBeforeBonus := 1056766, restrictionAfterBeta := 51655, restrictionAfterBonus := 1057614, updateProofs := some (121217, 121143), numericProof := 53630, slack := 2}
noncomputable def case775 : PhysicalCase := ⟨0,193,.south,.push 219 (.stay 245),frame775⟩
theorem frame775_checked : CountedLocalCaseData.check data frame775 = true := by decide +kernel
theorem case775_fitted : fits case775 = true := by decide +kernel
noncomputable def frame776 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 20, changes := [(220, true), (219, false)], beforeBeta := 5439691, beforeBonus := 5832728, afterBeta := 5439691, afterBonus := 5832717, preBeta := 5439691, preBonus := 5833486, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1060533, restrictionAfterBeta := 8531, restrictionAfterBonus := 1061134, updateProofs := some (125145, 125071), numericProof := 53876, slack := 2}
noncomputable def case776 : PhysicalCase := ⟨0,218,.east,.push 219 (.stay 220),frame776⟩
theorem frame776_checked : CountedLocalCaseData.check data frame776 = true := by decide +kernel
theorem case776_fitted : fits case776 = true := by decide +kernel
noncomputable def frame777 : CountedLocalCase.Frame := {bindings := [(218, false), (219, true), (220, false)], budget := 20, changes := [(218, true), (219, false)], beforeBeta := 5439691, beforeBonus := 5832718, afterBeta := 5439691, afterBonus := 5832717, preBeta := 5439691, preBonus := 5833489, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1065338, restrictionAfterBeta := 8531, restrictionAfterBonus := 1067862, updateProofs := some (129041, 128967), numericProof := 55958, slack := 0}
noncomputable def case777 : PhysicalCase := ⟨0,220,.west,.push 219 (.stay 218),frame777⟩
theorem frame777_checked : CountedLocalCaseData.check data frame777 = true := by decide +kernel
theorem case777_fitted : fits case777 = true := by decide +kernel
noncomputable def frame778 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 20, changes := [(194, true), (220, false)], beforeBeta := 5439691, beforeBonus := 5832741, afterBeta := 5439691, afterBonus := 5832718, preBeta := 5439691, preBonus := 5833492, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1069390, restrictionAfterBeta := 8531, restrictionAfterBonus := 1069914, updateProofs := some (131971, 131897), numericProof := 56283, slack := 1}
noncomputable def case778 : PhysicalCase := ⟨0,246,.north,.push 220 (.stay 194),frame778⟩
theorem frame778_checked : CountedLocalCaseData.check data frame778 = true := by decide +kernel
theorem case778_fitted : fits case778 = true := by decide +kernel
noncomputable def frame779 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 20, changes := [(246, true), (220, false)], beforeBeta := 5439691, beforeBonus := 5832720, afterBeta := 5439691, afterBonus := 5832718, preBeta := 5439691, preBonus := 5833495, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1074228, restrictionAfterBeta := 8531, restrictionAfterBonus := 1076969, updateProofs := some (137164, 137090), numericProof := 56748, slack := 1}
noncomputable def case779 : PhysicalCase := ⟨0,194,.south,.push 220 (.stay 246),frame779⟩
theorem frame779_checked : CountedLocalCaseData.check data frame779 = true := by decide +kernel
theorem case779_fitted : fits case779 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
