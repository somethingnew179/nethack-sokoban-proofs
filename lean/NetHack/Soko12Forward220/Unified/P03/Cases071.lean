import NetHack.Soko12Forward220.Unified.P03.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban
noncomputable def frame852 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 17, changes := [(372, true), (371, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 5834826, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343259, restrictionAfterBeta := 8531, restrictionAfterBonus := 1343263, updateProofs := some (340681, 378588), numericProof := 77269, slack := 2}
noncomputable def case852 : PhysicalCase := ⟨3,370,.east,.push 371 (.stay 372),frame852⟩
theorem frame852_checked : CountedLocalCaseData.check data frame852 = true := by decide +kernel
theorem case852_fitted : fits case852 = true := by decide +kernel
noncomputable def frame853 : CountedLocalCase.Frame := {bindings := [(370, false), (371, true), (372, false)], budget := 17, changes := [(370, true), (371, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832880, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (346314, 378592), numericProof := 77270, slack := 2}
noncomputable def case853 : PhysicalCase := ⟨3,372,.west,.push 371 (.stay 370),frame853⟩
theorem frame853_checked : CountedLocalCaseData.check data frame853 = true := by decide +kernel
theorem case853_fitted : fits case853 = true := by decide +kernel
noncomputable def frame854 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 17, changes := [(373, true), (372, false)], beforeBeta := 5439691, beforeBonus := 5832880, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1343267, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (351172, 346315), numericProof := 77271, slack := 1}
noncomputable def case854 : PhysicalCase := ⟨3,371,.east,.push 372 (.stay 373),frame854⟩
theorem frame854_checked : CountedLocalCaseData.check data frame854 = true := by decide +kernel
theorem case854_fitted : fits case854 = true := by decide +kernel
noncomputable def frame855 : CountedLocalCase.Frame := {bindings := [(371, false), (372, true), (373, false)], budget := 17, changes := [(371, true), (372, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (356024, 351173), numericProof := 77272, slack := 0}
noncomputable def case855 : PhysicalCase := ⟨3,373,.west,.push 372 (.stay 371),frame855⟩
theorem frame855_checked : CountedLocalCaseData.check data frame855 = true := by decide +kernel
theorem case855_fitted : fits case855 = true := by decide +kernel
noncomputable def frame856 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 17, changes := [(374, true), (373, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (360885, 356025), numericProof := 77273, slack := 1}
noncomputable def case856 : PhysicalCase := ⟨3,372,.east,.push 373 (.stay 374),frame856⟩
theorem frame856_checked : CountedLocalCaseData.check data frame856 = true := by decide +kernel
theorem case856_fitted : fits case856 = true := by decide +kernel
noncomputable def frame857 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 17, changes := [(372, true), (373, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (365740, 360886), numericProof := 77273, slack := 1}
noncomputable def case857 : PhysicalCase := ⟨3,374,.west,.push 373 (.stay 372),frame857⟩
theorem frame857_checked : CountedLocalCaseData.check data frame857 = true := by decide +kernel
theorem case857_fitted : fits case857 = true := by decide +kernel
noncomputable def frame858 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 17, changes := [(348, true), (374, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (370586, 365741), numericProof := 77274, slack := 1}
noncomputable def case858 : PhysicalCase := ⟨3,400,.north,.push 374 (.stay 348),frame858⟩
theorem frame858_checked : CountedLocalCaseData.check data frame858 = true := by decide +kernel
theorem case858_fitted : fits case858 = true := by decide +kernel
noncomputable def frame859 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 17, changes := [(400, true), (374, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (375453, 370587), numericProof := 77274, slack := 1}
noncomputable def case859 : PhysicalCase := ⟨3,348,.south,.push 374 (.stay 400),frame859⟩
theorem frame859_checked : CountedLocalCaseData.check data frame859 = true := by decide +kernel
theorem case859_fitted : fits case859 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P03
