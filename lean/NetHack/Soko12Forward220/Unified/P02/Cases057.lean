import NetHack.Soko12Forward220.Unified.P02.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban
noncomputable def frame684 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 18, changes := [(134, true), (133, false)], beforeBeta := 5439688, beforeBonus := 5832834, afterBeta := 5439689, afterBonus := 5832832, preBeta := 5440615, preBonus := 5834363, restrictionBeforeBeta := 924238, restrictionBeforeBonus := 1340689, restrictionAfterBeta := 924312, restrictionAfterBonus := 1340693, updateProofs := some (1060, 377561), numericProof := 76262, slack := 0}
noncomputable def case684 : PhysicalCase := ⟨2,132,.east,.push 133 (.stay 134),frame684⟩
theorem frame684_checked : CountedLocalCaseData.check data frame684 = true := by decide +kernel
theorem case684_fitted : fits case684 = true := by decide +kernel
noncomputable def frame685 : CountedLocalCase.Frame := {bindings := [(132, false), (133, true), (134, false)], budget := 18, changes := [(132, true), (133, false)], beforeBeta := 5112151, beforeBonus := 5832830, afterBeta := 5439689, afterBonus := 5832832, preBeta := 5440606, preBonus := 5834366, restrictionBeforeBeta := 924356, restrictionBeforeBonus := 1340700, restrictionAfterBeta := 924402, restrictionAfterBonus := 1340704, updateProofs := some (1136, 377568), numericProof := 76263, slack := 2}
noncomputable def case685 : PhysicalCase := ⟨2,134,.west,.push 133 (.stay 132),frame685⟩
theorem frame685_checked : CountedLocalCaseData.check data frame685 = true := by decide +kernel
theorem case685_fitted : fits case685 = true := by decide +kernel
noncomputable def frame686 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 18, changes := [(108, true), (134, false)], beforeBeta := 5439695, beforeBonus := 5832833, afterBeta := 5112151, afterBonus := 5832830, preBeta := 5112183, preBonus := 5834369, restrictionBeforeBeta := 924450, restrictionBeforeBonus := 1340718, restrictionAfterBeta := 924524, restrictionAfterBonus := 1340722, updateProofs := some (1218, 377575), numericProof := 76268, slack := 0}
noncomputable def case686 : PhysicalCase := ⟨2,160,.north,.push 134 (.stay 108),frame686⟩
theorem frame686_checked : CountedLocalCaseData.check data frame686 = true := by decide +kernel
theorem case686_fitted : fits case686 = true := by decide +kernel
noncomputable def frame687 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 18, changes := [(160, true), (134, false)], beforeBeta := 5439685, beforeBonus := 5832829, afterBeta := 5112151, afterBonus := 5832830, preBeta := 5113909, preBonus := 5834372, restrictionBeforeBeta := 924573, restrictionBeforeBonus := 1340726, restrictionAfterBeta := 924620, restrictionAfterBonus := 1340729, updateProofs := some (1493, 377582), numericProof := 76273, slack := 2}
noncomputable def case687 : PhysicalCase := ⟨2,108,.south,.push 134 (.stay 160),frame687⟩
theorem frame687_checked : CountedLocalCaseData.check data frame687 = true := by decide +kernel
theorem case687_fitted : fits case687 = true := by decide +kernel
noncomputable def frame688 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 18, changes := [(135, true), (134, false)], beforeBeta := 5439689, beforeBonus := 5832832, afterBeta := 5112151, afterBonus := 5832830, preBeta := 5112183, preBonus := 0, restrictionBeforeBeta := 924654, restrictionBeforeBonus := 1340736, restrictionAfterBeta := 924749, restrictionAfterBonus := 3, updateProofs := some (1575, 377589), numericProof := 76274, slack := 14}
noncomputable def case688 : PhysicalCase := ⟨2,133,.east,.push 134 (.stay 135),frame688⟩
theorem frame688_checked : CountedLocalCaseData.check data frame688 = true := by decide +kernel
theorem case688_fitted : fits case688 = true := by decide +kernel
noncomputable def frame689 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 18, changes := [(133, true), (134, false)], beforeBeta := 5439690, beforeBonus := 5832831, afterBeta := 5112151, afterBonus := 5832830, preBeta := 5113918, preBonus := 5834375, restrictionBeforeBeta := 924757, restrictionBeforeBonus := 1340743, restrictionAfterBeta := 924839, restrictionAfterBonus := 1340750, updateProofs := some (1639, 377596), numericProof := 76309, slack := 2}
noncomputable def case689 : PhysicalCase := ⟨2,135,.west,.push 134 (.stay 133),frame689⟩
theorem frame689_checked : CountedLocalCaseData.check data frame689 = true := by decide +kernel
theorem case689_fitted : fits case689 = true := by decide +kernel
noncomputable def frame690 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 18, changes := [(115, true), (141, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (1701, 1640), numericProof := 76310, slack := 1}
noncomputable def case690 : PhysicalCase := ⟨2,167,.north,.push 141 (.stay 115),frame690⟩
theorem frame690_checked : CountedLocalCaseData.check data frame690 = true := by decide +kernel
theorem case690_fitted : fits case690 = true := by decide +kernel
noncomputable def frame691 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 18, changes := [(167, true), (141, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2115, 1702), numericProof := 76311, slack := 0}
noncomputable def case691 : PhysicalCase := ⟨2,115,.south,.push 141 (.stay 167),frame691⟩
theorem frame691_checked : CountedLocalCaseData.check data frame691 = true := by decide +kernel
theorem case691_fitted : fits case691 = true := by decide +kernel
noncomputable def frame692 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 18, changes := [(142, true), (141, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2265, 2116), numericProof := 76312, slack := 1}
noncomputable def case692 : PhysicalCase := ⟨2,140,.east,.push 141 (.stay 142),frame692⟩
theorem frame692_checked : CountedLocalCaseData.check data frame692 = true := by decide +kernel
theorem case692_fitted : fits case692 = true := by decide +kernel
noncomputable def frame693 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 18, changes := [(140, true), (141, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439692, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2377, 2266), numericProof := 76313, slack := 1}
noncomputable def case693 : PhysicalCase := ⟨2,142,.west,.push 141 (.stay 140),frame693⟩
theorem frame693_checked : CountedLocalCaseData.check data frame693 = true := by decide +kernel
theorem case693_fitted : fits case693 = true := by decide +kernel
noncomputable def frame694 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 18, changes := [(116, true), (142, false)], beforeBeta := 5439696, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2430, 2378), numericProof := 76314, slack := 1}
noncomputable def case694 : PhysicalCase := ⟨2,168,.north,.push 142 (.stay 116),frame694⟩
theorem frame694_checked : CountedLocalCaseData.check data frame694 = true := by decide +kernel
theorem case694_fitted : fits case694 = true := by decide +kernel
noncomputable def frame695 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 18, changes := [(168, true), (142, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2717, 2431), numericProof := 76314, slack := 1}
noncomputable def case695 : PhysicalCase := ⟨2,116,.south,.push 142 (.stay 168),frame695⟩
theorem frame695_checked : CountedLocalCaseData.check data frame695 = true := by decide +kernel
theorem case695_fitted : fits case695 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P02
