import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame732 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 19, changes := [(161, true), (187, false)], beforeBeta := 5439691, beforeBonus := 5832782, afterBeta := 5439698, afterBonus := 5832781, preBeta := 5439690, preBonus := 5834016, restrictionBeforeBeta := 952399, restrictionBeforeBonus := 1337119, restrictionAfterBeta := 7685, restrictionAfterBonus := 1337121, updateProofs := some (30444, 376190), numericProof := 75679, slack := 2}
noncomputable def case732 : PhysicalCase := ⟨1,213,.north,.push 187 (.stay 161),frame732⟩
theorem frame732_checked : CountedLocalCaseData.check data frame732 = true := by decide +kernel
theorem case732_fitted : fits case732 = true := by decide +kernel
noncomputable def frame733 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 19, changes := [(213, true), (187, false)], beforeBeta := 5439690, beforeBonus := 5832777, afterBeta := 5439698, afterBonus := 5832781, preBeta := 5439690, preBonus := 5834019, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1337142, restrictionAfterBeta := 7685, restrictionAfterBonus := 1337149, updateProofs := some (31856, 376197), numericProof := 75683, slack := 0}
noncomputable def case733 : PhysicalCase := ⟨1,161,.south,.push 187 (.stay 213),frame733⟩
theorem frame733_checked : CountedLocalCaseData.check data frame733 = true := by decide +kernel
theorem case733_fitted : fits case733 = true := by decide +kernel
noncomputable def frame734 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 19, changes := [(163, true), (189, false)], beforeBeta := 5439691, beforeBonus := 5832785, afterBeta := 5439691, afterBonus := 5832793, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337151, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (32294, 376199), numericProof := 75684, slack := 7}
noncomputable def case734 : PhysicalCase := ⟨1,215,.north,.push 189 (.stay 163),frame734⟩
theorem frame734_checked : CountedLocalCaseData.check data frame734 = true := by decide +kernel
theorem case734_fitted : fits case734 = true := by decide +kernel
noncomputable def frame735 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 19, changes := [(215, true), (189, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832793, preBeta := 5439691, preBonus := 5834023, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337153, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337155, updateProofs := some (34524, 376201), numericProof := 75685, slack := 0}
noncomputable def case735 : PhysicalCase := ⟨1,163,.south,.push 189 (.stay 215),frame735⟩
theorem frame735_checked : CountedLocalCaseData.check data frame735 = true := by decide +kernel
theorem case735_fitted : fits case735 = true := by decide +kernel
noncomputable def frame736 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 19, changes := [(164, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832786, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337157, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (35000, 376203), numericProof := 75686, slack := 6}
noncomputable def case736 : PhysicalCase := ⟨1,216,.north,.push 190 (.stay 164),frame736⟩
theorem frame736_checked : CountedLocalCaseData.check data frame736 = true := by decide +kernel
theorem case736_fitted : fits case736 = true := by decide +kernel
noncomputable def frame737 : CountedLocalCase.Frame := {bindings := [(164, false), (190, true), (216, false)], budget := 19, changes := [(216, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832786, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337157, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (37936, 376205), numericProof := 75687, slack := 2}
noncomputable def case737 : PhysicalCase := ⟨1,164,.south,.push 190 (.stay 216),frame737⟩
theorem frame737_checked : CountedLocalCaseData.check data frame737 = true := by decide +kernel
theorem case737_fitted : fits case737 = true := by decide +kernel
noncomputable def frame738 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 19, changes := [(191, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832793, afterBeta := 5439691, afterBonus := 5832786, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337159, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (39482, 376207), numericProof := 75688, slack := 2}
noncomputable def case738 : PhysicalCase := ⟨1,189,.east,.push 190 (.stay 191),frame738⟩
theorem frame738_checked : CountedLocalCaseData.check data frame738 = true := by decide +kernel
theorem case738_fitted : fits case738 = true := by decide +kernel
noncomputable def frame739 : CountedLocalCase.Frame := {bindings := [(189, false), (190, true), (191, false)], budget := 19, changes := [(189, true), (190, false)], beforeBeta := 5439691, beforeBonus := 5832788, afterBeta := 5439691, afterBonus := 5832786, preBeta := 5439691, preBonus := 5834024, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337161, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337163, updateProofs := some (40870, 376209), numericProof := 75692, slack := 0}
noncomputable def case739 : PhysicalCase := ⟨1,191,.west,.push 190 (.stay 189),frame739⟩
theorem frame739_checked : CountedLocalCaseData.check data frame739 = true := by decide +kernel
theorem case739_fitted : fits case739 = true := by decide +kernel
noncomputable def frame740 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 19, changes := [(192, true), (191, false)], beforeBeta := 5439691, beforeBonus := 5832786, afterBeta := 5439691, afterBonus := 5832788, preBeta := 5440852, preBonus := 0, restrictionBeforeBeta := 44389, restrictionBeforeBonus := 1337165, restrictionAfterBeta := 935300, restrictionAfterBonus := 3, updateProofs := some (42814, 376211), numericProof := 75693, slack := 2}
noncomputable def case740 : PhysicalCase := ⟨1,190,.east,.push 191 (.stay 192),frame740⟩
theorem frame740_checked : CountedLocalCaseData.check data frame740 = true := by decide +kernel
theorem case740_fitted : fits case740 = true := by decide +kernel
noncomputable def frame741 : CountedLocalCase.Frame := {bindings := [(190, false), (191, true), (192, false)], budget := 19, changes := [(190, true), (191, false)], beforeBeta := 5439699, beforeBonus := 5832791, afterBeta := 5439691, afterBonus := 5832788, preBeta := 5439691, preBonus := 5834027, restrictionBeforeBeta := 46376, restrictionBeforeBonus := 1337167, restrictionAfterBeta := 44389, restrictionAfterBonus := 1337169, updateProofs := some (44466, 376213), numericProof := 75694, slack := 0}
noncomputable def case741 : PhysicalCase := ⟨1,192,.west,.push 191 (.stay 190),frame741⟩
theorem frame741_checked : CountedLocalCaseData.check data frame741 = true := by decide +kernel
theorem case741_fitted : fits case741 = true := by decide +kernel
noncomputable def frame742 : CountedLocalCase.Frame := {bindings := [(166, false), (192, true), (218, false)], budget := 19, changes := [(166, true), (192, false)], beforeBeta := 5439691, beforeBonus := 5832811, afterBeta := 5439699, afterBonus := 5832791, preBeta := 5439972, preBonus := 5834029, restrictionBeforeBeta := 967905, restrictionBeforeBonus := 1337171, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337173, updateProofs := some (45652, 376215), numericProof := 75698, slack := 2}
noncomputable def case742 : PhysicalCase := ⟨1,218,.north,.push 192 (.stay 166),frame742⟩
theorem frame742_checked : CountedLocalCaseData.check data frame742 = true := by decide +kernel
theorem case742_fitted : fits case742 = true := by decide +kernel
noncomputable def frame743 : CountedLocalCase.Frame := {bindings := [(166, false), (192, true), (218, false)], budget := 19, changes := [(218, true), (192, false)], beforeBeta := 5439691, beforeBonus := 5832792, afterBeta := 5439699, afterBonus := 5832791, preBeta := 5439972, preBonus := 5834032, restrictionBeforeBeta := 967905, restrictionBeforeBonus := 1337175, restrictionAfterBeta := 969324, restrictionAfterBonus := 1337177, updateProofs := some (49659, 376217), numericProof := 75700, slack := 2}
noncomputable def case743 : PhysicalCase := ⟨1,166,.south,.push 192 (.stay 218),frame743⟩
theorem frame743_checked : CountedLocalCaseData.check data frame743 = true := by decide +kernel
theorem case743_fitted : fits case743 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
