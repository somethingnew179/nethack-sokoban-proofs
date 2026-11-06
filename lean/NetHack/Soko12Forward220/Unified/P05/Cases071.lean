import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame852 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 15, changes := [(322, true), (348, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (318891, 314055), numericProof := 78311, slack := 1}
noncomputable def case852 : PhysicalCase := ⟨5,374,.north,.push 348 (.stay 322),frame852⟩
theorem frame852_checked : CountedLocalCaseData.check data frame852 = true := by decide +kernel
theorem case852_fitted : fits case852 = true := by decide +kernel
noncomputable def frame853 : CountedLocalCase.Frame := {bindings := [(322, false), (348, true), (374, false)], budget := 15, changes := [(374, true), (348, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (323752, 318892), numericProof := 78311, slack := 1}
noncomputable def case853 : PhysicalCase := ⟨5,322,.south,.push 348 (.stay 374),frame853⟩
theorem frame853_checked : CountedLocalCaseData.check data frame853 = true := by decide +kernel
theorem case853_fitted : fits case853 = true := by decide +kernel
noncomputable def frame854 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 15, changes := [(345, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345228, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (329389, 379097), numericProof := 78312, slack := 0}
noncomputable def case854 : PhysicalCase := ⟨5,397,.north,.push 371 (.stay 345),frame854⟩
theorem frame854_checked : CountedLocalCaseData.check data frame854 = true := by decide +kernel
theorem case854_fitted : fits case854 = true := by decide +kernel
noncomputable def frame855 : CountedLocalCase.Frame := {bindings := [(345, false), (371, true), (397, false)], budget := 15, changes := [(397, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345228, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (335039, 379099), numericProof := 78313, slack := 2}
noncomputable def case855 : PhysicalCase := ⟨5,345,.south,.push 371 (.stay 397),frame855⟩
theorem frame855_checked : CountedLocalCaseData.check data frame855 = true := by decide +kernel
theorem case855_fitted : fits case855 = true := by decide +kernel
noncomputable def frame856 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 15, changes := [(372, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 5835273, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345230, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345232, updateProofs := some (340681, 379101), numericProof := 78314, slack := 2}
noncomputable def case856 : PhysicalCase := ⟨5,370,.east,.push 371 (.stay 372),frame856⟩
theorem frame856_checked : CountedLocalCaseData.check data frame856 = true := by decide +kernel
theorem case856_fitted : fits case856 = true := by decide +kernel
noncomputable def frame857 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 15, changes := [(370, true), (371, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (346314, 379103), numericProof := 78315, slack := 2}
noncomputable def case857 : PhysicalCase := ⟨5,372,.west,.push 371 (.stay 370),frame857⟩
theorem frame857_checked : CountedLocalCaseData.check data frame857 = true := by decide +kernel
theorem case857_fitted : fits case857 = true := by decide +kernel
noncomputable def frame858 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 15, changes := [(373, true), (372, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345234, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (351172, 346315), numericProof := 78316, slack := 1}
noncomputable def case858 : PhysicalCase := ⟨5,371,.east,.push 372 (.stay 373),frame858⟩
theorem frame858_checked : CountedLocalCaseData.check data frame858 = true := by decide +kernel
theorem case858_fitted : fits case858 = true := by decide +kernel
noncomputable def frame859 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 15, changes := [(371, true), (372, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (356024, 351173), numericProof := 78317, slack := 0}
noncomputable def case859 : PhysicalCase := ⟨5,373,.west,.push 372 (.stay 371),frame859⟩
theorem frame859_checked : CountedLocalCaseData.check data frame859 = true := by decide +kernel
theorem case859_fitted : fits case859 = true := by decide +kernel
noncomputable def frame860 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 15, changes := [(374, true), (373, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (360885, 356025), numericProof := 78318, slack := 1}
noncomputable def case860 : PhysicalCase := ⟨5,372,.east,.push 373 (.stay 374),frame860⟩
theorem frame860_checked : CountedLocalCaseData.check data frame860 = true := by decide +kernel
theorem case860_fitted : fits case860 = true := by decide +kernel
noncomputable def frame861 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 15, changes := [(372, true), (373, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (365740, 360886), numericProof := 78318, slack := 1}
noncomputable def case861 : PhysicalCase := ⟨5,374,.west,.push 373 (.stay 372),frame861⟩
theorem frame861_checked : CountedLocalCaseData.check data frame861 = true := by decide +kernel
theorem case861_fitted : fits case861 = true := by decide +kernel
noncomputable def frame862 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 15, changes := [(348, true), (374, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (370586, 365741), numericProof := 78319, slack := 1}
noncomputable def case862 : PhysicalCase := ⟨5,400,.north,.push 374 (.stay 348),frame862⟩
theorem frame862_checked : CountedLocalCaseData.check data frame862 = true := by decide +kernel
theorem case862_fitted : fits case862 = true := by decide +kernel
noncomputable def frame863 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 15, changes := [(400, true), (374, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (375453, 370587), numericProof := 78319, slack := 1}
noncomputable def case863 : PhysicalCase := ⟨5,348,.south,.push 374 (.stay 400),frame863⟩
theorem frame863_checked : CountedLocalCaseData.check data frame863 = true := by decide +kernel
theorem case863_fitted : fits case863 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
