import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame732 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 15, changes := [(159, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5440930, preBonus := 0, restrictionBeforeBeta := 20208, restrictionBeforeBonus := 1345100, restrictionAfterBeta := 943566, restrictionAfterBonus := 3, updateProofs := some (21949, 378973), numericProof := 78194, slack := 0}
noncomputable def case732 : PhysicalCase := ⟨5,211,.north,.push 185 (.stay 159),frame732⟩
theorem frame732_checked : CountedLocalCaseData.check data frame732 = true := by decide +kernel
theorem case732_fitted : fits case732 = true := by decide +kernel
noncomputable def frame733 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 15, changes := [(211, true), (185, false)], beforeBeta := 5439694, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 19677, restrictionBeforeBonus := 1345100, restrictionAfterBeta := 20208, restrictionAfterBonus := 3, updateProofs := some (23648, 378975), numericProof := 78195, slack := 2}
noncomputable def case733 : PhysicalCase := ⟨5,159,.south,.push 185 (.stay 211),frame733⟩
theorem frame733_checked : CountedLocalCaseData.check data frame733 = true := by decide +kernel
theorem case733_fitted : fits case733 = true := by decide +kernel
noncomputable def frame734 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 15, changes := [(186, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832910, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5440955, preBonus := 5835240, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1345102, restrictionAfterBeta := 946126, restrictionAfterBonus := 1345104, updateProofs := some (24871, 378977), numericProof := 78199, slack := 0}
noncomputable def case734 : PhysicalCase := ⟨5,184,.east,.push 185 (.stay 186),frame734⟩
theorem frame734_checked : CountedLocalCaseData.check data frame734 = true := by decide +kernel
theorem case734_fitted : fits case734 = true := by decide +kernel
noncomputable def frame735 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 15, changes := [(184, true), (185, false)], beforeBeta := 5439697, beforeBonus := 5832911, afterBeta := 5439691, afterBonus := 5832909, preBeta := 5439691, preBonus := 5835242, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1345106, restrictionAfterBeta := 79701, restrictionAfterBonus := 1345108, updateProofs := some (25998, 378979), numericProof := 78200, slack := 2}
noncomputable def case735 : PhysicalCase := ⟨5,186,.west,.push 185 (.stay 184),frame735⟩
theorem frame735_checked : CountedLocalCaseData.check data frame735 = true := by decide +kernel
theorem case735_fitted : fits case735 = true := by decide +kernel
noncomputable def frame736 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 15, changes := [(160, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832911, afterBeta := 5439697, afterBonus := 5832911, preBeta := 5440974, preBonus := 0, restrictionBeforeBeta := 947685, restrictionBeforeBonus := 1345110, restrictionAfterBeta := 948362, restrictionAfterBonus := 3, updateProofs := some (26750, 378981), numericProof := 78201, slack := 0}
noncomputable def case736 : PhysicalCase := ⟨5,212,.north,.push 186 (.stay 160),frame736⟩
theorem frame736_checked : CountedLocalCaseData.check data frame736 = true := by decide +kernel
theorem case736_fitted : fits case736 = true := by decide +kernel
noncomputable def frame737 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 15, changes := [(212, true), (186, false)], beforeBeta := 5439695, beforeBonus := 5832909, afterBeta := 5439697, afterBonus := 5832911, preBeta := 5440026, preBonus := 0, restrictionBeforeBeta := 8199, restrictionBeforeBonus := 1345112, restrictionAfterBeta := 949615, restrictionAfterBonus := 3, updateProofs := some (27961, 378983), numericProof := 78202, slack := 2}
noncomputable def case737 : PhysicalCase := ⟨5,160,.south,.push 186 (.stay 212),frame737⟩
theorem frame737_checked : CountedLocalCaseData.check data frame737 = true := by decide +kernel
theorem case737_fitted : fits case737 = true := by decide +kernel
noncomputable def frame738 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 15, changes := [(187, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439697, afterBonus := 5832911, preBeta := 5441000, preBonus := 5835244, restrictionBeforeBeta := 949847, restrictionBeforeBonus := 1345114, restrictionAfterBeta := 951000, restrictionAfterBonus := 1345116, updateProofs := some (28839, 378985), numericProof := 78206, slack := 4}
noncomputable def case738 : PhysicalCase := ⟨5,185,.east,.push 186 (.stay 187),frame738⟩
theorem frame738_checked : CountedLocalCaseData.check data frame738 = true := by decide +kernel
theorem case738_fitted : fits case738 = true := by decide +kernel
noncomputable def frame739 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 15, changes := [(185, true), (186, false)], beforeBeta := 5439698, beforeBonus := 0, afterBeta := 5439697, afterBonus := 5832911, preBeta := 5440026, preBonus := 0, restrictionBeforeBeta := 951446, restrictionBeforeBonus := 3, restrictionAfterBeta := 952128, restrictionAfterBonus := 3, updateProofs := some (29636, 378987), numericProof := 78207, slack := 2}
noncomputable def case739 : PhysicalCase := ⟨5,187,.west,.push 186 (.stay 185),frame739⟩
theorem frame739_checked : CountedLocalCaseData.check data frame739 = true := by decide +kernel
theorem case739_fitted : fits case739 = true := by decide +kernel
noncomputable def frame740 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 15, changes := [(161, true), (187, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439698, afterBonus := 0, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 952399, restrictionBeforeBonus := 3, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (30444, 29637), numericProof := 78208, slack := 2}
noncomputable def case740 : PhysicalCase := ⟨5,213,.north,.push 187 (.stay 161),frame740⟩
theorem frame740_checked : CountedLocalCaseData.check data frame740 = true := by decide +kernel
theorem case740_fitted : fits case740 = true := by decide +kernel
noncomputable def frame741 : CountedLocalCase.Frame := {bindings := [(161, false), (187, true), (213, false)], budget := 15, changes := [(213, true), (187, false)], beforeBeta := 5439690, beforeBonus := 5832909, afterBeta := 5439698, afterBonus := 0, preBeta := 5439690, preBonus := 0, restrictionBeforeBeta := 7685, restrictionBeforeBonus := 1345118, restrictionAfterBeta := 7685, restrictionAfterBonus := 3, updateProofs := some (31856, 30445), numericProof := 78209, slack := 0}
noncomputable def case741 : PhysicalCase := ⟨5,161,.south,.push 187 (.stay 213),frame741⟩
theorem frame741_checked : CountedLocalCaseData.check data frame741 = true := by decide +kernel
theorem case741_fitted : fits case741 = true := by decide +kernel
noncomputable def frame742 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 15, changes := [(163, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (32294, 31857), numericProof := 78210, slack := 7}
noncomputable def case742 : PhysicalCase := ⟨5,215,.north,.push 189 (.stay 163),frame742⟩
theorem frame742_checked : CountedLocalCaseData.check data frame742 = true := by decide +kernel
theorem case742_fitted : fits case742 = true := by decide +kernel
noncomputable def frame743 : CountedLocalCase.Frame := {bindings := [(163, false), (189, true), (215, false)], budget := 15, changes := [(215, true), (189, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (34524, 32295), numericProof := 78211, slack := 0}
noncomputable def case743 : PhysicalCase := ⟨5,163,.south,.push 189 (.stay 215),frame743⟩
theorem frame743_checked : CountedLocalCaseData.check data frame743 = true := by decide +kernel
theorem case743_fitted : fits case743 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
