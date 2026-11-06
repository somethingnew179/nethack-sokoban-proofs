import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame684 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 17, changes := [(133, true), (132, false)], beforeBeta := 5439686, beforeBonus := 5832868, afterBeta := 5439688, afterBonus := 5832869, preBeta := 5440596, preBonus := 5834678, restrictionBeforeBeta := 924040, restrictionBeforeBonus := 1342757, restrictionAfterBeta := 924109, restrictionAfterBonus := 1342760, updateProofs := some (902, 378230), numericProof := 77029, slack := 0}
noncomputable def case684 : PhysicalCase := ⟨3,131,.east,.push 132 (.stay 133),frame684⟩
theorem frame684_checked : CountedLocalCaseData.check data frame684 = true := by decide +kernel
theorem case684_fitted : fits case684 = true := by decide +kernel
noncomputable def frame685 : CountedLocalCase.Frame := {bindings := [(131, false), (132, true), (133, false)], budget := 17, changes := [(131, true), (132, false)], beforeBeta := 5439689, beforeBonus := 5832860, afterBeta := 5439688, afterBonus := 5832869, preBeta := 5439706, preBonus := 0, restrictionBeforeBeta := 924166, restrictionBeforeBonus := 1342763, restrictionAfterBeta := 924229, restrictionAfterBonus := 3, updateProofs := some (955, 378234), numericProof := 77030, slack := 12}
noncomputable def case685 : PhysicalCase := ⟨3,133,.west,.push 132 (.stay 131),frame685⟩
theorem frame685_checked : CountedLocalCaseData.check data frame685 = true := by decide +kernel
theorem case685_fitted : fits case685 = true := by decide +kernel
noncomputable def frame686 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 17, changes := [(134, true), (133, false)], beforeBeta := 5439688, beforeBonus := 5832869, afterBeta := 5439689, afterBonus := 5832860, preBeta := 5440615, preBonus := 5834682, restrictionBeforeBeta := 924238, restrictionBeforeBonus := 1342767, restrictionAfterBeta := 924312, restrictionAfterBonus := 1342770, updateProofs := some (1060, 378238), numericProof := 77034, slack := 0}
noncomputable def case686 : PhysicalCase := ⟨3,132,.east,.push 133 (.stay 134),frame686⟩
theorem frame686_checked : CountedLocalCaseData.check data frame686 = true := by decide +kernel
theorem case686_fitted : fits case686 = true := by decide +kernel
noncomputable def frame687 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 17, changes := [(132, true), (133, false)], beforeBeta := 5112151, beforeBonus := 5832858, afterBeta := 5439689, afterBonus := 5832860, preBeta := 5440606, preBonus := 5834685, restrictionBeforeBeta := 924356, restrictionBeforeBonus := 1342774, restrictionAfterBeta := 924402, restrictionAfterBonus := 1342777, updateProofs := some (1136, 378242), numericProof := 77035, slack := 2}
noncomputable def case687 : PhysicalCase := ⟨3,134,.west,.push 133 (.stay 132),frame687⟩
theorem frame687_checked : CountedLocalCaseData.check data frame687 = true := by decide +kernel
theorem case687_fitted : fits case687 = true := by decide +kernel
noncomputable def frame688 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 17, changes := [(108, true), (134, false)], beforeBeta := 5439695, beforeBonus := 5832861, afterBeta := 5112151, afterBonus := 5832858, preBeta := 5112183, preBonus := 5834688, restrictionBeforeBeta := 924450, restrictionBeforeBonus := 1342781, restrictionAfterBeta := 924524, restrictionAfterBonus := 1342784, updateProofs := some (1218, 378246), numericProof := 77039, slack := 0}
noncomputable def case688 : PhysicalCase := ⟨3,160,.north,.push 134 (.stay 108),frame688⟩
theorem frame688_checked : CountedLocalCaseData.check data frame688 = true := by decide +kernel
theorem case688_fitted : fits case688 = true := by decide +kernel
noncomputable def frame689 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 17, changes := [(160, true), (134, false)], beforeBeta := 5439685, beforeBonus := 5832857, afterBeta := 5112151, afterBonus := 5832858, preBeta := 5113909, preBonus := 5834691, restrictionBeforeBeta := 924573, restrictionBeforeBonus := 1342787, restrictionAfterBeta := 924620, restrictionAfterBonus := 1342789, updateProofs := some (1493, 378250), numericProof := 77043, slack := 2}
noncomputable def case689 : PhysicalCase := ⟨3,108,.south,.push 134 (.stay 160),frame689⟩
theorem frame689_checked : CountedLocalCaseData.check data frame689 = true := by decide +kernel
theorem case689_fitted : fits case689 = true := by decide +kernel
noncomputable def frame690 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 17, changes := [(135, true), (134, false)], beforeBeta := 5439689, beforeBonus := 5832860, afterBeta := 5112151, afterBonus := 5832858, preBeta := 5112183, preBonus := 0, restrictionBeforeBeta := 924654, restrictionBeforeBonus := 1342793, restrictionAfterBeta := 924749, restrictionAfterBonus := 3, updateProofs := some (1575, 378254), numericProof := 77044, slack := 14}
noncomputable def case690 : PhysicalCase := ⟨3,133,.east,.push 134 (.stay 135),frame690⟩
theorem frame690_checked : CountedLocalCaseData.check data frame690 = true := by decide +kernel
theorem case690_fitted : fits case690 = true := by decide +kernel
noncomputable def frame691 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 17, changes := [(133, true), (134, false)], beforeBeta := 5439690, beforeBonus := 5832859, afterBeta := 5112151, afterBonus := 5832858, preBeta := 5113918, preBonus := 5834694, restrictionBeforeBeta := 924757, restrictionBeforeBonus := 1342797, restrictionAfterBeta := 924839, restrictionAfterBonus := 1342801, updateProofs := some (1639, 378258), numericProof := 77050, slack := 2}
noncomputable def case691 : PhysicalCase := ⟨3,135,.west,.push 134 (.stay 133),frame691⟩
theorem frame691_checked : CountedLocalCaseData.check data frame691 = true := by decide +kernel
theorem case691_fitted : fits case691 = true := by decide +kernel
noncomputable def frame692 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 17, changes := [(115, true), (141, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (1701, 1640), numericProof := 77051, slack := 1}
noncomputable def case692 : PhysicalCase := ⟨3,167,.north,.push 141 (.stay 115),frame692⟩
theorem frame692_checked : CountedLocalCaseData.check data frame692 = true := by decide +kernel
theorem case692_fitted : fits case692 = true := by decide +kernel
noncomputable def frame693 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 17, changes := [(167, true), (141, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2115, 1702), numericProof := 77052, slack := 0}
noncomputable def case693 : PhysicalCase := ⟨3,115,.south,.push 141 (.stay 167),frame693⟩
theorem frame693_checked : CountedLocalCaseData.check data frame693 = true := by decide +kernel
theorem case693_fitted : fits case693 = true := by decide +kernel
noncomputable def frame694 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 17, changes := [(142, true), (141, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2265, 2116), numericProof := 77053, slack := 1}
noncomputable def case694 : PhysicalCase := ⟨3,140,.east,.push 141 (.stay 142),frame694⟩
theorem frame694_checked : CountedLocalCaseData.check data frame694 = true := by decide +kernel
theorem case694_fitted : fits case694 = true := by decide +kernel
noncomputable def frame695 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 17, changes := [(140, true), (141, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2377, 2266), numericProof := 77054, slack := 1}
noncomputable def case695 : PhysicalCase := ⟨3,142,.west,.push 141 (.stay 140),frame695⟩
theorem frame695_checked : CountedLocalCaseData.check data frame695 = true := by decide +kernel
theorem case695_fitted : fits case695 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
