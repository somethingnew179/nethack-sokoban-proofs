import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame852 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 19, changes := [(374, true), (373, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338632, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (360885, 377463), numericProof := 75911, slack := 1}
noncomputable def case852 : PhysicalCase := ⟨1,372,.east,.push 373 (.stay 374),frame852⟩
theorem frame852_checked : CountedLocalCaseData.check data frame852 = true := by decide +kernel
theorem case852_fitted : fits case852 = true := by decide +kernel
noncomputable def frame853 : CountedLocalCase.Frame := {bindings := [(372, false), (373, true), (374, false)], budget := 19, changes := [(372, true), (373, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338632, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (365740, 377465), numericProof := 75911, slack := 1}
noncomputable def case853 : PhysicalCase := ⟨1,374,.west,.push 373 (.stay 372),frame853⟩
theorem frame853_checked : CountedLocalCaseData.check data frame853 = true := by decide +kernel
theorem case853_fitted : fits case853 = true := by decide +kernel
noncomputable def frame854 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 19, changes := [(348, true), (374, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338634, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (370586, 377467), numericProof := 75912, slack := 1}
noncomputable def case854 : PhysicalCase := ⟨1,400,.north,.push 374 (.stay 348),frame854⟩
theorem frame854_checked : CountedLocalCaseData.check data frame854 = true := by decide +kernel
theorem case854_fitted : fits case854 = true := by decide +kernel
noncomputable def frame855 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 19, changes := [(400, true), (374, false)], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1338634, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (375453, 377469), numericProof := 75912, slack := 1}
noncomputable def case855 : PhysicalCase := ⟨1,348,.south,.push 374 (.stay 400),frame855⟩
theorem frame855_checked : CountedLocalCaseData.check data frame855 = true := by decide +kernel
theorem case855_fitted : fits case855 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
