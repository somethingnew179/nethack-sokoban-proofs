import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame684 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 20, changes := [(135, true), (134, false)], beforeBeta := 5439689, beforeBonus := 5832755, afterBeta := 5112151, afterBonus := 5832752, preBeta := 5112183, preBonus := 0, restrictionBeforeBeta := 924654, restrictionBeforeBonus := 924746, restrictionAfterBeta := 924749, restrictionAfterBonus := 3, updateProofs := some (1575, 1567), numericProof := 3676, slack := 14}
noncomputable def case684 : PhysicalCase := ⟨0,133,.east,.push 134 (.stay 135),frame684⟩
theorem frame684_checked : CountedLocalCaseData.check data frame684 = true := by decide +kernel
theorem case684_fitted : fits case684 = true := by decide +kernel
noncomputable def frame685 : CountedLocalCase.Frame := {bindings := [(133, false), (134, true), (135, false)], budget := 20, changes := [(133, true), (134, false)], beforeBeta := 5439690, beforeBonus := 5832754, afterBeta := 5112151, afterBonus := 5832752, preBeta := 5113918, preBonus := 5833259, restrictionBeforeBeta := 924757, restrictionBeforeBonus := 924838, restrictionAfterBeta := 924839, restrictionAfterBonus := 924878, updateProofs := some (1639, 1633), numericProof := 4336, slack := 2}
noncomputable def case685 : PhysicalCase := ⟨0,135,.west,.push 134 (.stay 133),frame685⟩
theorem frame685_checked : CountedLocalCaseData.check data frame685 = true := by decide +kernel
theorem case685_fitted : fits case685 = true := by decide +kernel
noncomputable def frame686 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 20, changes := [(115, true), (141, false)], beforeBeta := 5439691, beforeBonus := 5832726, afterBeta := 5439692, afterBonus := 5832733, preBeta := 5439687, preBonus := 5833262, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 925101, restrictionAfterBeta := 829, restrictionAfterBonus := 925123, updateProofs := some (1701, 1673), numericProof := 5785, slack := 1}
noncomputable def case686 : PhysicalCase := ⟨0,167,.north,.push 141 (.stay 115),frame686⟩
theorem frame686_checked : CountedLocalCaseData.check data frame686 = true := by decide +kernel
theorem case686_fitted : fits case686 = true := by decide +kernel
noncomputable def frame687 : CountedLocalCase.Frame := {bindings := [(115, false), (141, true), (167, false)], budget := 20, changes := [(167, true), (141, false)], beforeBeta := 5439687, beforeBonus := 5832735, afterBeta := 5439692, afterBonus := 5832733, preBeta := 5439687, preBonus := 5833265, restrictionBeforeBeta := 829, restrictionBeforeBonus := 925309, restrictionAfterBeta := 829, restrictionAfterBonus := 925325, updateProofs := some (2115, 2076), numericProof := 7223, slack := 0}
noncomputable def case687 : PhysicalCase := ⟨0,115,.south,.push 141 (.stay 167),frame687⟩
theorem frame687_checked : CountedLocalCaseData.check data frame687 = true := by decide +kernel
theorem case687_fitted : fits case687 = true := by decide +kernel
noncomputable def frame688 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 20, changes := [(142, true), (141, false)], beforeBeta := 5439691, beforeBonus := 5832729, afterBeta := 5439692, afterBonus := 5832733, preBeta := 5439687, preBonus := 5833268, restrictionBeforeBeta := 924904, restrictionBeforeBonus := 925442, restrictionAfterBeta := 829, restrictionAfterBonus := 925520, updateProofs := some (2265, 2237), numericProof := 10038, slack := 1}
noncomputable def case688 : PhysicalCase := ⟨0,140,.east,.push 141 (.stay 142),frame688⟩
theorem frame688_checked : CountedLocalCaseData.check data frame688 = true := by decide +kernel
theorem case688_fitted : fits case688 = true := by decide +kernel
noncomputable def frame689 : CountedLocalCase.Frame := {bindings := [(140, false), (141, true), (142, false)], budget := 20, changes := [(140, true), (141, false)], beforeBeta := 5439687, beforeBonus := 5832742, afterBeta := 5439692, afterBonus := 5832733, preBeta := 5439687, preBonus := 5833271, restrictionBeforeBeta := 829, restrictionBeforeBonus := 925556, restrictionAfterBeta := 829, restrictionAfterBonus := 925577, updateProofs := some (2377, 2349), numericProof := 10254, slack := 1}
noncomputable def case689 : PhysicalCase := ⟨0,142,.west,.push 141 (.stay 140),frame689⟩
theorem frame689_checked : CountedLocalCaseData.check data frame689 = true := by decide +kernel
theorem case689_fitted : fits case689 = true := by decide +kernel
noncomputable def frame690 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 20, changes := [(116, true), (142, false)], beforeBeta := 5439696, beforeBonus := 5832722, afterBeta := 5439687, afterBonus := 5832742, preBeta := 5439687, preBonus := 5833274, restrictionBeforeBeta := 12959, restrictionBeforeBonus := 925879, restrictionAfterBeta := 829, restrictionAfterBonus := 925903, updateProofs := some (2430, 2410), numericProof := 11128, slack := 1}
noncomputable def case690 : PhysicalCase := ⟨0,168,.north,.push 142 (.stay 116),frame690⟩
theorem frame690_checked : CountedLocalCaseData.check data frame690 = true := by decide +kernel
theorem case690_fitted : fits case690 = true := by decide +kernel
noncomputable def frame691 : CountedLocalCase.Frame := {bindings := [(116, false), (142, true), (168, false)], budget := 20, changes := [(168, true), (142, false)], beforeBeta := 5439687, beforeBonus := 5832732, afterBeta := 5439687, afterBonus := 5832742, preBeta := 5439687, preBonus := 5833277, restrictionBeforeBeta := 829, restrictionBeforeBonus := 926088, restrictionAfterBeta := 829, restrictionAfterBonus := 926100, updateProofs := some (2717, 2686), numericProof := 11339, slack := 1}
noncomputable def case691 : PhysicalCase := ⟨0,116,.south,.push 142 (.stay 168),frame691⟩
theorem frame691_checked : CountedLocalCaseData.check data frame691 = true := by decide +kernel
theorem case691_fitted : fits case691 = true := by decide +kernel
noncomputable def frame692 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 20, changes := [(143, true), (142, false)], beforeBeta := 5439692, beforeBonus := 5832733, afterBeta := 5439687, afterBonus := 5832742, preBeta := 5439687, preBonus := 5833280, restrictionBeforeBeta := 949, restrictionBeforeBonus := 926213, restrictionAfterBeta := 829, restrictionAfterBonus := 926240, updateProofs := some (2806, 2786), numericProof := 11859, slack := 1}
noncomputable def case692 : PhysicalCase := ⟨0,141,.east,.push 142 (.stay 143),frame692⟩
theorem frame692_checked : CountedLocalCaseData.check data frame692 = true := by decide +kernel
theorem case692_fitted : fits case692 = true := by decide +kernel
noncomputable def frame693 : CountedLocalCase.Frame := {bindings := [(141, false), (142, true), (143, false)], budget := 20, changes := [(141, true), (142, false)], beforeBeta := 5439687, beforeBonus := 5832727, afterBeta := 5439687, afterBonus := 5832742, preBeta := 5439687, preBonus := 5833283, restrictionBeforeBeta := 829, restrictionBeforeBonus := 926321, restrictionAfterBeta := 829, restrictionAfterBonus := 926352, updateProofs := some (2883, 2863), numericProof := 12248, slack := 1}
noncomputable def case693 : PhysicalCase := ⟨0,143,.west,.push 142 (.stay 141),frame693⟩
theorem frame693_checked : CountedLocalCaseData.check data frame693 = true := by decide +kernel
theorem case693_fitted : fits case693 = true := by decide +kernel
noncomputable def frame694 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 20, changes := [(117, true), (143, false)], beforeBeta := 5439687, beforeBonus := 5832725, afterBeta := 5439687, afterBonus := 5832727, preBeta := 5439687, preBonus := 5833286, restrictionBeforeBeta := 829, restrictionBeforeBonus := 926530, restrictionAfterBeta := 829, restrictionAfterBonus := 926547, updateProofs := some (2936, 2916), numericProof := 12396, slack := 1}
noncomputable def case694 : PhysicalCase := ⟨0,169,.north,.push 143 (.stay 117),frame694⟩
theorem frame694_checked : CountedLocalCaseData.check data frame694 = true := by decide +kernel
theorem case694_fitted : fits case694 = true := by decide +kernel
noncomputable def frame695 : CountedLocalCase.Frame := {bindings := [(117, false), (143, true), (169, false)], budget := 20, changes := [(169, true), (143, false)], beforeBeta := 5439687, beforeBonus := 5832731, afterBeta := 5439687, afterBonus := 5832727, preBeta := 5439687, preBonus := 5833289, restrictionBeforeBeta := 829, restrictionBeforeBonus := 926623, restrictionAfterBeta := 829, restrictionAfterBonus := 926636, updateProofs := some (3540, 3509), numericProof := 12545, slack := 1}
noncomputable def case695 : PhysicalCase := ⟨0,117,.south,.push 143 (.stay 169),frame695⟩
theorem frame695_checked : CountedLocalCaseData.check data frame695 = true := by decide +kernel
theorem case695_fitted : fits case695 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
