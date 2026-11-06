import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame684 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 19, changes := [(108, true), (134, false)], beforeBeta := 5439695, beforeBonus := 5832776, afterBeta := 5112151, afterBonus := 5832773, preBeta := 5112183, preBonus := 5833913, restrictionBeforeBeta := 924450, restrictionBeforeBonus := 1336345, restrictionAfterBeta := 924524, restrictionAfterBonus := 1336357, updateProofs := some (1218, 375641), numericProof := 75126, slack := 0}
noncomputable def case684 : PhysicalCase := ⟨1,160,.north,.push 134 (.stay 108),frame684⟩
theorem frame684_checked : CountedLocalCaseData.check data frame684 = true := by decide +kernel
theorem case684_fitted : fits case684 = true := by decide +kernel
noncomputable def frame685 : CountedLocalCase.Frame := {bindings := [(108, false), (134, true), (160, false)], budget := 19, changes := [(160, true), (134, false)], beforeBeta := 5439685, beforeBonus := 5832772, afterBeta := 5112151, afterBonus := 5832773, preBeta := 5113909, preBonus := 5833916, restrictionBeforeBeta := 924573, restrictionBeforeBonus := 1336372, restrictionAfterBeta := 924620, restrictionAfterBonus := 1336376, updateProofs := some (1493, 375663), numericProof := 75132, slack := 2}
noncomputable def case685 : PhysicalCase := ⟨1,108,.south,.push 134 (.stay 160),frame685⟩
theorem frame685_checked : CountedLocalCaseData.check data frame685 = true := by decide +kernel
theorem case685_fitted : fits case685 = true := by decide +kernel
noncomputable def frame686 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 19, changes := [(135, true), (134, false)], beforeBeta := 5439689, beforeBonus := 5832775, afterBeta := 5112151, afterBonus := 5832773, preBeta := 5112183, preBonus := 0, restrictionBeforeBeta := 924654, restrictionBeforeBonus := 1336395, restrictionAfterBeta := 924749, restrictionAfterBonus := 3, updateProofs := some (1575, 375678), numericProof := 75133, slack := 14}
noncomputable def case686 : PhysicalCase := ⟨1,133,.east,.push 134 (.stay 135),frame686⟩
theorem frame686_checked : CountedLocalCaseData.check data frame686 = true := by decide +kernel
theorem case686_fitted : fits case686 = true := by decide +kernel
noncomputable def frame687 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 19, changes := [(133, true), (134, false)], beforeBeta := 5439690, beforeBonus := 5832774, afterBeta := 5112151, afterBonus := 5832773, preBeta := 5113918, preBonus := 5833919, restrictionBeforeBeta := 924757, restrictionBeforeBonus := 1336414, restrictionAfterBeta := 924839, restrictionAfterBonus := 1336426, updateProofs := some (1639, 375693), numericProof := 75194, slack := 2}
noncomputable def case687 : PhysicalCase := ⟨1,135,.west,.push 134 (.stay 133),frame687⟩
theorem frame687_checked : CountedLocalCaseData.check data frame687 = true := by decide +kernel
theorem case687_fitted : fits case687 = true := by decide +kernel
noncomputable def frame688 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 19, changes := [(115, true), (141, false)], beforeBeta := 5439691, beforeBonus := 5832798, afterBeta := 5439692, afterBonus := 5832801, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 1336428, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (1701, 375695), numericProof := 75198, slack := 1}
noncomputable def case688 : PhysicalCase := ⟨1,167,.north,.push 141 (.stay 115),frame688⟩
theorem frame688_checked : CountedLocalCaseData.check data frame688 = true := by decide +kernel
theorem case688_fitted : fits case688 = true := by decide +kernel
noncomputable def frame689 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 19, changes := [(167, true), (141, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439692, afterBonus := 5832801, preBeta := 5439687, preBonus := 5833923, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336430, restrictionAfterBeta := 829, restrictionAfterBonus := 1336432, updateProofs := some (2115, 375697), numericProof := 75202, slack := 0}
noncomputable def case689 : PhysicalCase := ⟨1,115,.south,.push 141 (.stay 167),frame689⟩
theorem frame689_checked : CountedLocalCaseData.check data frame689 = true := by decide +kernel
theorem case689_fitted : fits case689 = true := by decide +kernel
noncomputable def frame690 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 19, changes := [(142, true), (141, false)], beforeBeta := 5439691, beforeBonus := 5832800, afterBeta := 5439692, afterBonus := 5832801, preBeta := 5439687, preBonus := 5833925, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 1336434, restrictionAfterBeta := 829, restrictionAfterBonus := 1336436, updateProofs := some (2265, 375699), numericProof := 75206, slack := 1}
noncomputable def case690 : PhysicalCase := ⟨1,140,.east,.push 141 (.stay 142),frame690⟩
theorem frame690_checked : CountedLocalCaseData.check data frame690 = true := by decide +kernel
theorem case690_fitted : fits case690 = true := by decide +kernel
noncomputable def frame691 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 19, changes := [(140, true), (141, false)], beforeBeta := 5439687, beforeBonus := 0, afterBeta := 5439692, afterBonus := 5832801, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 3, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2377, 375701), numericProof := 75207, slack := 1}
noncomputable def case691 : PhysicalCase := ⟨1,142,.west,.push 141 (.stay 140),frame691⟩
theorem frame691_checked : CountedLocalCaseData.check data frame691 = true := by decide +kernel
theorem case691_fitted : fits case691 = true := by decide +kernel
noncomputable def frame692 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 19, changes := [(116, true), (142, false)], beforeBeta := 5439696, beforeBonus := 5832805, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 1336438, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2430, 2378), numericProof := 75208, slack := 1}
noncomputable def case692 : PhysicalCase := ⟨1,168,.north,.push 142 (.stay 116),frame692⟩
theorem frame692_checked : CountedLocalCaseData.check data frame692 = true := by decide +kernel
theorem case692_fitted : fits case692 = true := by decide +kernel
noncomputable def frame693 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 19, changes := [(168, true), (142, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336440, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2717, 2431), numericProof := 75208, slack := 1}
noncomputable def case693 : PhysicalCase := ⟨1,116,.south,.push 142 (.stay 168),frame693⟩
theorem frame693_checked : CountedLocalCaseData.check data frame693 = true := by decide +kernel
theorem case693_fitted : fits case693 = true := by decide +kernel
noncomputable def frame694 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 19, changes := [(143, true), (142, false)], beforeBeta := 5439692, beforeBonus := 5832801, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 949, restrictionBeforeBonus := 1336442, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2806, 2718), numericProof := 75209, slack := 1}
noncomputable def case694 : PhysicalCase := ⟨1,141,.east,.push 142 (.stay 143),frame694⟩
theorem frame694_checked : CountedLocalCaseData.check data frame694 = true := by decide +kernel
theorem case694_fitted : fits case694 = true := by decide +kernel
noncomputable def frame695 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 19, changes := [(141, true), (142, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439687, afterBonus := 0, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336444, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (2883, 2807), numericProof := 75209, slack := 1}
noncomputable def case695 : PhysicalCase := ⟨1,143,.west,.push 142 (.stay 141),frame695⟩
theorem frame695_checked : CountedLocalCaseData.check data frame695 = true := by decide +kernel
theorem case695_fitted : fits case695 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
