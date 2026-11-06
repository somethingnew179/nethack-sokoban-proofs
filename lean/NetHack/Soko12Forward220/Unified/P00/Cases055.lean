import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame660 : CountedLocalCase.Frame := {bindings := [(372, false), (373, false)], budget := 20, changes := [], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 5832707, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 888483, restrictionAfterBeta := 8531, restrictionAfterBonus := 888483, updateProofs := none, numericProof := 315, slack := 0}
noncomputable def case660 : PhysicalCase := ⟨0,399,.northWest,.walk 372,frame660⟩
theorem frame660_checked : CountedLocalCaseData.check data frame660 = true := by decide +kernel
theorem case660_fitted : fits case660 = true := by decide +kernel
noncomputable def frame661 : CountedLocalCase.Frame := {bindings := [(374, false), (400, false)], budget := 20, changes := [], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 5832707, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 913332, restrictionAfterBeta := 8531, restrictionAfterBonus := 913332, updateProofs := none, numericProof := 320, slack := 0}
noncomputable def case661 : PhysicalCase := ⟨0,400,.north,.walk 374,frame661⟩
theorem frame661_checked : CountedLocalCaseData.check data frame661 = true := by decide +kernel
theorem case661_fitted : fits case661 = true := by decide +kernel
noncomputable def frame662 : CountedLocalCase.Frame := {bindings := [(400, false)], budget := 20, changes := [], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 5832707, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 923669, restrictionAfterBeta := 8531, restrictionAfterBonus := 923669, updateProofs := none, numericProof := 322, slack := 0}
noncomputable def case662 : PhysicalCase := ⟨0,400,.west,.walk 399,frame662⟩
theorem frame662_checked : CountedLocalCaseData.check data frame662 = true := by decide +kernel
theorem case662_fitted : fits case662 = true := by decide +kernel
noncomputable def frame663 : CountedLocalCase.Frame := {bindings := [(373, false), (400, false)], budget := 20, changes := [], beforeBeta := 5439691, beforeBonus := 5832707, afterBeta := 5439691, afterBonus := 5832707, preBeta := 5439691, preBonus := 5832707, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 908549, restrictionAfterBeta := 8531, restrictionAfterBonus := 908549, updateProofs := none, numericProof := 319, slack := 0}
noncomputable def case663 : PhysicalCase := ⟨0,400,.northWest,.walk 373,frame663⟩
theorem frame663_checked : CountedLocalCaseData.check data frame663 = true := by decide +kernel
theorem case663_fitted : fits case663 = true := by decide +kernel
noncomputable def frame664 : CountedLocalCase.Frame := {bindings := [(29, false), (30, true)], budget := 20, changes := [(30, false)], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 5832769, preBeta := 5439685, preBonus := 5833227, restrictionBeforeBeta := 0, restrictionBeforeBonus := 923672, restrictionAfterBeta := 0, restrictionAfterBonus := 923673, updateProofs := some (4, 3), numericProof := 323, slack := 0}
noncomputable def case664 : PhysicalCase := ⟨0,29,.east,.push 30 (.fill 32),frame664⟩
theorem frame664_checked : CountedLocalCaseData.check data frame664 = true := by decide +kernel
theorem case664_fitted : fits case664 = true := by decide +kernel
noncomputable def frame665 : CountedLocalCase.Frame := {bindings := [(29, false), (30, true)], budget := 20, changes := [(29, true), (30, false)], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 0, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (6, 5), numericProof := 324, slack := 18}
noncomputable def case665 : PhysicalCase := ⟨0,31,.west,.push 30 (.stay 29),frame665⟩
theorem frame665_checked : CountedLocalCaseData.check data frame665 = true := by decide +kernel
theorem case665_fitted : fits case665 = true := by decide +kernel
noncomputable def frame666 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 20, changes := [(30, true), (56, false)], beforeBeta := 5439685, beforeBonus := 5832763, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5833228, restrictionBeforeBeta := 0, restrictionBeforeBonus := 923676, restrictionAfterBeta := 0, restrictionAfterBonus := 923677, updateProofs := some (12, 11), numericProof := 325, slack := 0}
noncomputable def case666 : PhysicalCase := ⟨0,82,.north,.push 56 (.stay 30),frame666⟩
theorem frame666_checked : CountedLocalCaseData.check data frame666 = true := by decide +kernel
theorem case666_fitted : fits case666 = true := by decide +kernel
noncomputable def frame667 : CountedLocalCase.Frame := {bindings := [(30, false), (56, true), (82, false)], budget := 20, changes := [(82, true), (56, false)], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := some (18, 17), numericProof := 326, slack := 2}
noncomputable def case667 : PhysicalCase := ⟨0,30,.south,.push 56 (.stay 82),frame667⟩
theorem frame667_checked : CountedLocalCaseData.check data frame667 = true := by decide +kernel
theorem case667_fitted : fits case667 = true := by decide +kernel
noncomputable def frame668 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 20, changes := [(56, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832759, afterBeta := 5439685, afterBonus := 5832763, preBeta := 5439685, preBonus := 5833230, restrictionBeforeBeta := 23, restrictionBeforeBonus := 923683, restrictionAfterBeta := 23, restrictionAfterBonus := 923685, updateProofs := some (28, 27), numericProof := 327, slack := 0}
noncomputable def case668 : PhysicalCase := ⟨0,108,.north,.push 82 (.stay 56),frame668⟩
theorem frame668_checked : CountedLocalCaseData.check data frame668 = true := by decide +kernel
theorem case668_fitted : fits case668 = true := by decide +kernel
noncomputable def frame669 : CountedLocalCase.Frame := {bindings := [(56, false), (82, true), (108, false)], budget := 20, changes := [(108, true), (82, false)], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 5832763, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 23, restrictionBeforeBonus := 923689, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (43, 41), numericProof := 328, slack := 2}
noncomputable def case669 : PhysicalCase := ⟨0,56,.south,.push 82 (.stay 108),frame669⟩
theorem frame669_checked : CountedLocalCaseData.check data frame669 = true := by decide +kernel
theorem case669_fitted : fits case669 = true := by decide +kernel
noncomputable def frame670 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 20, changes := [(82, true), (108, false)], beforeBeta := 5112151, beforeBonus := 5832752, afterBeta := 5439685, afterBonus := 5832759, preBeta := 5112151, preBonus := 5833232, restrictionBeforeBeta := 536, restrictionBeforeBonus := 923705, restrictionAfterBeta := 536, restrictionAfterBonus := 923715, updateProofs := some (65, 63), numericProof := 329, slack := 0}
noncomputable def case670 : PhysicalCase := ⟨0,134,.north,.push 108 (.stay 82),frame670⟩
theorem frame670_checked : CountedLocalCaseData.check data frame670 = true := by decide +kernel
theorem case670_fitted : fits case670 = true := by decide +kernel
noncomputable def frame671 : CountedLocalCase.Frame := {bindings := [(82, false), (108, true), (134, false)], budget := 20, changes := [(134, true), (108, false)], beforeBeta := 5439685, beforeBonus := 5832763, afterBeta := 5439685, afterBonus := 5832759, preBeta := 4784969, preBonus := 0, restrictionBeforeBeta := 923716, restrictionBeforeBonus := 923728, restrictionAfterBeta := 534, restrictionAfterBonus := 3, updateProofs := some (120, 113), numericProof := 330, slack := 2}
noncomputable def case671 : PhysicalCase := ⟨0,82,.south,.push 108 (.stay 134),frame671⟩
theorem frame671_checked : CountedLocalCaseData.check data frame671 = true := by decide +kernel
theorem case671_fitted : fits case671 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
