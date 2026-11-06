import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame852 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 20, changes := [(348, true), (374, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1330386, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (370586, 370509), numericProof := 74766, slack := 1}
noncomputable def case852 : PhysicalCase := ⟨0,400,.north,.push 374 (.stay 348),frame852⟩
theorem frame852_checked : CountedLocalCaseData.check data frame852 = true := by decide +kernel
theorem case852_fitted : fits case852 = true := by decide +kernel
noncomputable def frame853 : CountedLocalCase.Frame := {bindings := [(348, false), (374, true), (400, false)], budget := 20, changes := [(400, true), (374, false)], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1330386, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (375453, 375376), numericProof := 74766, slack := 1}
noncomputable def case853 : PhysicalCase := ⟨0,348,.south,.push 374 (.stay 400),frame853⟩
theorem frame853_checked : CountedLocalCaseData.check data frame853 = true := by decide +kernel
theorem case853_fitted : fits case853 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
