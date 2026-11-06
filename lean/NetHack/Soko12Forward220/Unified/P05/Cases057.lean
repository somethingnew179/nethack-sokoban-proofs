import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame684 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 15, changes := [(105, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832910, afterBeta := 5439686, afterBonus := 5832910, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1345048, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (180, 378917), numericProof := 78141, slack := 1}
noncomputable def case684 : PhysicalCase := ⟨5,157,.north,.push 131 (.stay 105),frame684⟩
theorem frame684_checked : CountedLocalCaseData.check data frame684 = true := by decide +kernel
theorem case684_fitted : fits case684 = true := by decide +kernel
noncomputable def frame685 : CountedLocalCase.Frame := {bindings := [(105, false), (131, true), (157, false)], budget := 15, changes := [(157, true), (131, false)], beforeBeta := 5439686, beforeBonus := 5832910, afterBeta := 5439686, afterBonus := 5832910, preBeta := 5439686, preBonus := 0, restrictionBeforeBeta := 45, restrictionBeforeBonus := 1345048, restrictionAfterBeta := 45, restrictionAfterBonus := 3, updateProofs := some (508, 378919), numericProof := 78141, slack := 1}
noncomputable def case685 : PhysicalCase := ⟨5,105,.south,.push 131 (.stay 157),frame685⟩
theorem frame685_checked : CountedLocalCaseData.check data frame685 = true := by decide +kernel
theorem case685_fitted : fits case685 = true := by decide +kernel
noncomputable def frame686 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 15, changes := [(106, true), (132, false)], beforeBeta := 5439693, beforeBonus := 5832910, afterBeta := 5439688, afterBonus := 5832910, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 923823, restrictionBeforeBonus := 1345050, restrictionAfterBeta := 923956, restrictionAfterBonus := 3, updateProofs := some (529, 378921), numericProof := 78142, slack := 12}
noncomputable def case686 : PhysicalCase := ⟨5,158,.north,.push 132 (.stay 106),frame686⟩
theorem frame686_checked : CountedLocalCaseData.check data frame686 = true := by decide +kernel
theorem case686_fitted : fits case686 = true := by decide +kernel
noncomputable def frame687 : CountedLocalCase.Frame := {bindings := [(106, false), (132, true), (158, false)], budget := 15, changes := [(158, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832910, afterBeta := 5439688, afterBonus := 5832910, preBeta := 5440591, preBonus := 0, restrictionBeforeBeta := 923959, restrictionBeforeBonus := 1345050, restrictionAfterBeta := 924014, restrictionAfterBonus := 3, updateProofs := some (826, 378923), numericProof := 78143, slack := 2}
noncomputable def case687 : PhysicalCase := ⟨5,106,.south,.push 132 (.stay 158),frame687⟩
theorem frame687_checked : CountedLocalCaseData.check data frame687 = true := by decide +kernel
theorem case687_fitted : fits case687 = true := by decide +kernel
noncomputable def frame688 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 15, changes := [(133, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832910, afterBeta := 5439688, afterBonus := 5832910, preBeta := 5440596, preBonus := 0, restrictionBeforeBeta := 924040, restrictionBeforeBonus := 1345052, restrictionAfterBeta := 924109, restrictionAfterBonus := 3, updateProofs := some (902, 378925), numericProof := 78144, slack := 0}
noncomputable def case688 : PhysicalCase := ⟨5,131,.east,.push 132 (.stay 133),frame688⟩
theorem frame688_checked : CountedLocalCaseData.check data frame688 = true := by decide +kernel
theorem case688_fitted : fits case688 = true := by decide +kernel
noncomputable def frame689 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 15, changes := [(131, true), (132, false)], beforeBeta := 5439689, beforeBonus := 5832910, afterBeta := 5439688, afterBonus := 5832910, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 924166, restrictionBeforeBonus := 1345052, restrictionAfterBeta := 924229, restrictionAfterBonus := 3, updateProofs := some (955, 378927), numericProof := 78145, slack := 12}
noncomputable def case689 : PhysicalCase := ⟨5,133,.west,.push 132 (.stay 131),frame689⟩
theorem frame689_checked : CountedLocalCaseData.check data frame689 = true := by decide +kernel
theorem case689_fitted : fits case689 = true := by decide +kernel
noncomputable def frame690 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 15, changes := [(134, true), (133, false)], beforeBeta := 5439688, beforeBonus := 5832910, afterBeta := 5439689, afterBonus := 5832910, preBeta := 5440615, preBonus := 0, restrictionBeforeBeta := 924238, restrictionBeforeBonus := 1345054, restrictionAfterBeta := 924312, restrictionAfterBonus := 3, updateProofs := some (1060, 378929), numericProof := 78146, slack := 0}
noncomputable def case690 : PhysicalCase := ⟨5,132,.east,.push 133 (.stay 134),frame690⟩
theorem frame690_checked : CountedLocalCaseData.check data frame690 = true := by decide +kernel
theorem case690_fitted : fits case690 = true := by decide +kernel
noncomputable def frame691 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 15, changes := [(132, true), (133, false)], beforeBeta := 5112151, beforeBonus := 5832909, afterBeta := 5439689, afterBonus := 5832910, preBeta := 5440606, preBonus := 0, restrictionBeforeBeta := 924356, restrictionBeforeBonus := 1345056, restrictionAfterBeta := 924402, restrictionAfterBonus := 3, updateProofs := some (1136, 378931), numericProof := 78147, slack := 2}
noncomputable def case691 : PhysicalCase := ⟨5,134,.west,.push 133 (.stay 132),frame691⟩
theorem frame691_checked : CountedLocalCaseData.check data frame691 = true := by decide +kernel
theorem case691_fitted : fits case691 = true := by decide +kernel
noncomputable def frame692 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 15, changes := [(108, true), (134, false)], beforeBeta := 5439695, beforeBonus := 5832909, afterBeta := 5112151, afterBonus := 5832909, preBeta := 5112183, preBonus := 0, restrictionBeforeBeta := 924450, restrictionBeforeBonus := 1345058, restrictionAfterBeta := 924524, restrictionAfterBonus := 3, updateProofs := some (1218, 378933), numericProof := 78148, slack := 0}
noncomputable def case692 : PhysicalCase := ⟨5,160,.north,.push 134 (.stay 108),frame692⟩
theorem frame692_checked : CountedLocalCaseData.check data frame692 = true := by decide +kernel
theorem case692_fitted : fits case692 = true := by decide +kernel
noncomputable def frame693 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 15, changes := [(160, true), (134, false)], beforeBeta := 5439685, beforeBonus := 5832909, afterBeta := 5112151, afterBonus := 5832909, preBeta := 5113909, preBonus := 0, restrictionBeforeBeta := 924573, restrictionBeforeBonus := 1345058, restrictionAfterBeta := 924620, restrictionAfterBonus := 3, updateProofs := some (1493, 378935), numericProof := 78149, slack := 2}
noncomputable def case693 : PhysicalCase := ⟨5,108,.south,.push 134 (.stay 160),frame693⟩
theorem frame693_checked : CountedLocalCaseData.check data frame693 = true := by decide +kernel
theorem case693_fitted : fits case693 = true := by decide +kernel
noncomputable def frame694 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 15, changes := [(135, true), (134, false)], beforeBeta := 5439689, beforeBonus := 5832910, afterBeta := 5112151, afterBonus := 5832909, preBeta := 5112183, preBonus := 0, restrictionBeforeBeta := 924654, restrictionBeforeBonus := 1345060, restrictionAfterBeta := 924749, restrictionAfterBonus := 3, updateProofs := some (1575, 378937), numericProof := 78150, slack := 14}
noncomputable def case694 : PhysicalCase := ⟨5,133,.east,.push 134 (.stay 135),frame694⟩
theorem frame694_checked : CountedLocalCaseData.check data frame694 = true := by decide +kernel
theorem case694_fitted : fits case694 = true := by decide +kernel
noncomputable def frame695 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 15, changes := [(133, true), (134, false)], beforeBeta := 5439690, beforeBonus := 5832909, afterBeta := 5112151, afterBonus := 5832909, preBeta := 5113918, preBonus := 5835229, restrictionBeforeBeta := 924757, restrictionBeforeBonus := 1345062, restrictionAfterBeta := 924839, restrictionAfterBonus := 1345064, updateProofs := some (1639, 378939), numericProof := 78154, slack := 2}
noncomputable def case695 : PhysicalCase := ⟨5,135,.west,.push 134 (.stay 133),frame695⟩
theorem frame695_checked : CountedLocalCaseData.check data frame695 = true := by decide +kernel
theorem case695_fitted : fits case695 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
