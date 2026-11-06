import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame660 : CountedLocalCase.Frame := {bindings := [(373, false), (374, false)], budget := 19, changes := [], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5832807, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1336117, restrictionAfterBeta := 8531, restrictionAfterBonus := 1336117, updateProofs := none, numericProof := 75085, slack := 0}
noncomputable def case660 : PhysicalCase := ⟨1,399,.northEast,.walk 374,frame660⟩
theorem frame660_checked : CountedLocalCaseData.check data frame660 = true := by decide +kernel
theorem case660_fitted : fits case660 = true := by decide +kernel
noncomputable def frame661 : CountedLocalCase.Frame := {bindings := [(374, false), (400, false)], budget := 19, changes := [], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5832807, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1336121, restrictionAfterBeta := 8531, restrictionAfterBonus := 1336121, updateProofs := none, numericProof := 75087, slack := 0}
noncomputable def case661 : PhysicalCase := ⟨1,399,.northEast,.walk 374,frame661⟩
theorem frame661_checked : CountedLocalCaseData.check data frame661 = true := by decide +kernel
theorem case661_fitted : fits case661 = true := by decide +kernel
noncomputable def frame662 : CountedLocalCase.Frame := {bindings := [(372, false), (373, false)], budget := 19, changes := [], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5832807, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1336090, restrictionAfterBeta := 8531, restrictionAfterBonus := 1336090, updateProofs := none, numericProof := 75082, slack := 0}
noncomputable def case662 : PhysicalCase := ⟨1,399,.northWest,.walk 372,frame662⟩
theorem frame662_checked : CountedLocalCaseData.check data frame662 = true := by decide +kernel
theorem case662_fitted : fits case662 = true := by decide +kernel
noncomputable def frame663 : CountedLocalCase.Frame := {bindings := [(374, false), (400, false)], budget := 19, changes := [], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5832807, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1336121, restrictionAfterBeta := 8531, restrictionAfterBonus := 1336121, updateProofs := none, numericProof := 75087, slack := 0}
noncomputable def case663 : PhysicalCase := ⟨1,400,.north,.walk 374,frame663⟩
theorem frame663_checked : CountedLocalCaseData.check data frame663 = true := by decide +kernel
theorem case663_fitted : fits case663 = true := by decide +kernel
noncomputable def frame664 : CountedLocalCase.Frame := {bindings := [(400, false)], budget := 19, changes := [], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5832807, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1336144, restrictionAfterBeta := 8531, restrictionAfterBonus := 1336144, updateProofs := none, numericProof := 75089, slack := 0}
noncomputable def case664 : PhysicalCase := ⟨1,400,.west,.walk 399,frame664⟩
theorem frame664_checked : CountedLocalCaseData.check data frame664 = true := by decide +kernel
theorem case664_fitted : fits case664 = true := by decide +kernel
noncomputable def frame665 : CountedLocalCase.Frame := {bindings := [(373, false), (400, false)], budget := 19, changes := [], beforeBeta := 5439691, beforeBonus := 5832807, afterBeta := 5439691, afterBonus := 5832807, preBeta := 5439691, preBonus := 5832807, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1336119, restrictionAfterBeta := 8531, restrictionAfterBonus := 1336119, updateProofs := none, numericProof := 75086, slack := 0}
noncomputable def case665 : PhysicalCase := ⟨1,400,.northWest,.walk 373,frame665⟩
theorem frame665_checked : CountedLocalCaseData.check data frame665 = true := by decide +kernel
theorem case665_fitted : fits case665 = true := by decide +kernel
noncomputable def frame666 : CountedLocalCase.Frame := {bindings := [(29, false), (30, true)], budget := 19, changes := [(30, false)], beforeBeta := 5439685, beforeBonus := 5832770, afterBeta := 5439685, afterBonus := 5832826, preBeta := 5439685, preBonus := 5833893, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1336147, restrictionAfterBeta := 0, restrictionAfterBonus := 1336148, updateProofs := some (4, 375456), numericProof := 75090, slack := 0}
noncomputable def case666 : PhysicalCase := ⟨1,29,.east,.push 30 (.fill 33),frame666⟩
theorem frame666_checked : CountedLocalCaseData.check data frame666 = true := by decide +kernel
theorem case666_fitted : fits case666 = true := by decide +kernel
noncomputable def frame667 : CountedLocalCase.Frame := {bindings := [(29, false), (30, true)], budget := 19, changes := [(29, true), (30, false)], beforeBeta := 5439685, beforeBonus := 5832769, afterBeta := 5439685, afterBonus := 5832769, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1336150, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (6, 375457), numericProof := 75091, slack := 18}
noncomputable def case667 : PhysicalCase := ⟨1,31,.west,.push 30 (.stay 29),frame667⟩
theorem frame667_checked : CountedLocalCaseData.check data frame667 = true := by decide +kernel
theorem case667_fitted : fits case667 = true := by decide +kernel
noncomputable def frame668 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 19, changes := [(30, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832771, afterBeta := 5439685, afterBonus := 5832770, preBeta := 5439685, preBonus := 5833894, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1336153, restrictionAfterBeta := 0, restrictionAfterBonus := 1336154, updateProofs := some (12, 375461), numericProof := 75092, slack := 0}
noncomputable def case668 : PhysicalCase := ⟨1,82,.north,.push 56 (.stay 30),frame668⟩
theorem frame668_checked : CountedLocalCaseData.check data frame668 = true := by decide +kernel
theorem case668_fitted : fits case668 = true := by decide +kernel
noncomputable def frame669 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 19, changes := [(82, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832769, afterBeta := 5439685, afterBonus := 5832770, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 1336157, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (18, 375465), numericProof := 75093, slack := 2}
noncomputable def case669 : PhysicalCase := ⟨1,30,.south,.push 56 (.stay 82),frame669⟩
theorem frame669_checked : CountedLocalCaseData.check data frame669 = true := by decide +kernel
theorem case669_fitted : fits case669 = true := by decide +kernel
noncomputable def frame670 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 19, changes := [(56, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832772, afterBeta := 5439685, afterBonus := 5832771, preBeta := 5439685, preBonus := 5833896, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1336161, restrictionAfterBeta := 23, restrictionAfterBonus := 1336163, updateProofs := some (28, 375470), numericProof := 75094, slack := 0}
noncomputable def case670 : PhysicalCase := ⟨1,108,.north,.push 82 (.stay 56),frame670⟩
theorem frame670_checked : CountedLocalCaseData.check data frame670 = true := by decide +kernel
theorem case670_fitted : fits case670 = true := by decide +kernel
noncomputable def frame671 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 19, changes := [(108, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832770, afterBeta := 5439685, afterBonus := 5832771, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 23, restrictionBeforeBonus := 1336167, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (43, 375477), numericProof := 75095, slack := 2}
noncomputable def case671 : PhysicalCase := ⟨1,56,.south,.push 82 (.stay 108),frame671⟩
theorem frame671_checked : CountedLocalCaseData.check data frame671 = true := by decide +kernel
theorem case671_fitted : fits case671 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
