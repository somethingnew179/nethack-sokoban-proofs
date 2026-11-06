import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame732 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 20, changes := [(163, true), (189, false)], beforeBeta := 5439691, beforeBonus := 5832734, afterBeta := 5439691, afterBonus := 5832736, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 956657, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (32294, 32229), numericProof := 28954, slack := 7}
noncomputable def case732 : PhysicalCase := ⟨0,215,.north,.push 189 (.stay 163),frame732⟩
theorem frame732_checked : CountedLocalCaseData.check data frame732 = true := by decide +kernel
theorem case732_fitted : fits case732 = true := by decide +kernel
noncomputable def frame733 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 20, changes := [(215, true), (189, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832736, preBeta := 5439691, preBonus := 5833395, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 958458, restrictionAfterBeta := 8531, restrictionAfterBonus := 958868, updateProofs := some (34524, 34450), numericProof := 28955, slack := 0}
noncomputable def case733 : PhysicalCase := ⟨0,163,.south,.push 189 (.stay 215),frame733⟩
theorem frame733_checked : CountedLocalCaseData.check data frame733 = true := by decide +kernel
theorem case733_fitted : fits case733 = true := by decide +kernel
noncomputable def frame734 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 20, changes := [(164, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832730, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 960188, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (35000, 34935), numericProof := 28956, slack := 6}
noncomputable def case734 : PhysicalCase := ⟨0,216,.north,.push 190 (.stay 164),frame734⟩
theorem frame734_checked : CountedLocalCaseData.check data frame734 = true := by decide +kernel
theorem case734_fitted : fits case734 = true := by decide +kernel
noncomputable def frame735 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 20, changes := [(216, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832730, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 960188, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (37936, 37862), numericProof := 28957, slack := 2}
noncomputable def case735 : PhysicalCase := ⟨0,164,.south,.push 190 (.stay 216),frame735⟩
theorem frame735_checked : CountedLocalCaseData.check data frame735 = true := by decide +kernel
theorem case735_fitted : fits case735 = true := by decide +kernel
noncomputable def frame736 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 20, changes := [(191, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832736, afterBeta := 5439691, afterBonus := 5832730, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 961429, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (39482, 39417), numericProof := 28958, slack := 2}
noncomputable def case736 : PhysicalCase := ⟨0,189,.east,.push 190 (.stay 191),frame736⟩
theorem frame736_checked : CountedLocalCaseData.check data frame736 = true := by decide +kernel
theorem case736_fitted : fits case736 = true := by decide +kernel
noncomputable def frame737 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 20, changes := [(189, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832724, afterBeta := 5439691, afterBonus := 5832730, preBeta := 5439691, preBonus := 5833396, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 962790, restrictionAfterBeta := 8531, restrictionAfterBonus := 963869, updateProofs := some (40870, 40805), numericProof := 30556, slack := 0}
noncomputable def case737 : PhysicalCase := ⟨0,191,.west,.push 190 (.stay 189),frame737⟩
theorem frame737_checked : CountedLocalCaseData.check data frame737 = true := by decide +kernel
theorem case737_fitted : fits case737 = true := by decide +kernel
noncomputable def frame738 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 20, changes := [(192, true), (191, false)], beforeBeta := 5439691, beforeBonus := 5832730, afterBeta := 5439691, afterBonus := 5832724, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 965349, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (42814, 42745), numericProof := 30557, slack := 2}
noncomputable def case738 : PhysicalCase := ⟨0,190,.east,.push 191 (.stay 192),frame738⟩
theorem frame738_checked : CountedLocalCaseData.check data frame738 = true := by decide +kernel
theorem case738_fitted : fits case738 = true := by decide +kernel
noncomputable def frame739 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 20, changes := [(190, true), (191, false)], beforeBeta := 5439699, beforeBonus := 5832721, afterBeta := 5439691, afterBonus := 5832724, preBeta := 5439691, preBonus := 5833399, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 966778, restrictionAfterBeta := 44389, restrictionAfterBonus := 967836, updateProofs := some (44466, 44401), numericProof := 30558, slack := 0}
noncomputable def case739 : PhysicalCase := ⟨0,192,.west,.push 191 (.stay 190),frame739⟩
theorem frame739_checked : CountedLocalCaseData.check data frame739 = true := by decide +kernel
theorem case739_fitted : fits case739 = true := by decide +kernel
noncomputable def frame740 : CountedLocalCase.Frame := {bindings := [(166, false), (192, true), (218, false)], budget := 20, changes := [(166, true), (192, false)], beforeBeta := 5439691, beforeBonus := 5832728, afterBeta := 5439699, afterBonus := 5832721, preBeta := 5439972, preBonus := 5833401, restrictionBeforeBeta := 967905, restrictionBeforeBonus := 969323, restrictionAfterBeta := 969324, restrictionAfterBonus := 970087, updateProofs := some (45652, 45584), numericProof := 33325, slack := 2}
noncomputable def case740 : PhysicalCase := ⟨0,218,.north,.push 192 (.stay 166),frame740⟩
theorem frame740_checked : CountedLocalCaseData.check data frame740 = true := by decide +kernel
theorem case740_fitted : fits case740 = true := by decide +kernel
noncomputable def frame741 : CountedLocalCase.Frame := {bindings := [(166, false), (192, true), (218, false)], budget := 20, changes := [(218, true), (192, false)], beforeBeta := 5439691, beforeBonus := 5832723, afterBeta := 5439699, afterBonus := 5832721, preBeta := 5439972, preBonus := 5833404, restrictionBeforeBeta := 967905, restrictionBeforeBonus := 972045, restrictionAfterBeta := 969324, restrictionAfterBonus := 972531, updateProofs := some (49659, 49591), numericProof := 35422, slack := 2}
noncomputable def case741 : PhysicalCase := ⟨0,166,.south,.push 192 (.stay 218),frame741⟩
theorem frame741_checked : CountedLocalCaseData.check data frame741 = true := by decide +kernel
theorem case741_fitted : fits case741 = true := by decide +kernel
noncomputable def frame742 : CountedLocalCase.Frame := {bindings := [(191, false), (192, true), (193, false)], budget := 20, changes := [(193, true), (192, false)], beforeBeta := 5439691, beforeBonus := 5832724, afterBeta := 5439699, afterBonus := 5832721, preBeta := 5439972, preBonus := 5833407, restrictionBeforeBeta := 972596, restrictionBeforeBonus := 974470, restrictionAfterBeta := 969324, restrictionAfterBonus := 975611, updateProofs := some (52122, 52054), numericProof := 35423, slack := 2}
noncomputable def case742 : PhysicalCase := ⟨0,191,.east,.push 192 (.stay 193),frame742⟩
theorem frame742_checked : CountedLocalCaseData.check data frame742 = true := by decide +kernel
theorem case742_fitted : fits case742 = true := by decide +kernel
noncomputable def frame743 : CountedLocalCase.Frame := {bindings := [(191, false), (192, true), (193, false)], budget := 20, changes := [(191, true), (192, false)], beforeBeta := 5439700, beforeBonus := 5832719, afterBeta := 5439699, afterBonus := 5832721, preBeta := 5439972, preBonus := 5833409, restrictionBeforeBeta := 975681, restrictionBeforeBonus := 977320, restrictionAfterBeta := 969324, restrictionAfterBonus := 978510, updateProofs := some (54133, 54065), numericProof := 36654, slack := 0}
noncomputable def case743 : PhysicalCase := ⟨0,193,.west,.push 192 (.stay 191),frame743⟩
theorem frame743_checked : CountedLocalCaseData.check data frame743 = true := by decide +kernel
theorem case743_fitted : fits case743 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
