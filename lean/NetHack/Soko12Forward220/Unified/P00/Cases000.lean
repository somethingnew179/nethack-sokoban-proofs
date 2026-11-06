import NetHack.Soko12Forward220.Unified.P00.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban
noncomputable def frame000 : CountedLocalCase.Frame := {bindings := [(29, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 2, restrictionAfterBeta := 0, restrictionAfterBonus := 2, updateProofs := none, numericProof := 0, slack := 0}
noncomputable def case000 : PhysicalCase := ⟨0,29,.south,.walk 55,frame000⟩
theorem frame000_checked : CountedLocalCaseData.check data frame000 = true := by decide +kernel
theorem case000_fitted : fits case000 = true := by decide +kernel
noncomputable def frame001 : CountedLocalCase.Frame := {bindings := [(29, false), (30, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 0, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 5, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := none, numericProof := 1, slack := 0}
noncomputable def case001 : PhysicalCase := ⟨0,29,.east,.walk 30,frame001⟩
theorem frame001_checked : CountedLocalCaseData.check data frame001 = true := by decide +kernel
theorem case001_fitted : fits case001 = true := by decide +kernel
noncomputable def frame002 : CountedLocalCase.Frame := {bindings := [(29, false), (56, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 9, restrictionAfterBeta := 0, restrictionAfterBonus := 9, updateProofs := none, numericProof := 2, slack := 0}
noncomputable def case002 : PhysicalCase := ⟨0,29,.southEast,.walk 56,frame002⟩
theorem frame002_checked : CountedLocalCaseData.check data frame002 = true := by decide +kernel
theorem case002_fitted : fits case002 = true := by decide +kernel
noncomputable def frame003 : CountedLocalCase.Frame := {bindings := [(30, false), (56, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 11, updateProofs := none, numericProof := 3, slack := 0}
noncomputable def case003 : PhysicalCase := ⟨0,30,.south,.walk 56,frame003⟩
theorem frame003_checked : CountedLocalCaseData.check data frame003 = true := by decide +kernel
theorem case003_fitted : fits case003 = true := by decide +kernel
noncomputable def frame004 : CountedLocalCase.Frame := {bindings := [(30, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 0, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := none, numericProof := 4, slack := 0}
noncomputable def case004 : PhysicalCase := ⟨0,30,.east,.walk 31,frame004⟩
theorem frame004_checked : CountedLocalCaseData.check data frame004 = true := by decide +kernel
theorem case004_fitted : fits case004 = true := by decide +kernel
noncomputable def frame005 : CountedLocalCase.Frame := {bindings := [(29, false), (30, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 5, updateProofs := none, numericProof := 1, slack := 0}
noncomputable def case005 : PhysicalCase := ⟨0,30,.west,.walk 29,frame005⟩
theorem frame005_checked : CountedLocalCaseData.check data frame005 = true := by decide +kernel
theorem case005_fitted : fits case005 = true := by decide +kernel
noncomputable def frame006 : CountedLocalCase.Frame := {bindings := [(30, false), (56, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 11, updateProofs := none, numericProof := 3, slack := 0}
noncomputable def case006 : PhysicalCase := ⟨0,30,.southWest,.walk 55,frame006⟩
theorem frame006_checked : CountedLocalCaseData.check data frame006 = true := by decide +kernel
theorem case006_fitted : fits case006 = true := by decide +kernel
noncomputable def frame007 : CountedLocalCase.Frame := {bindings := [(29, false), (30, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 5, updateProofs := none, numericProof := 1, slack := 0}
noncomputable def case007 : PhysicalCase := ⟨0,30,.southWest,.walk 55,frame007⟩
theorem frame007_checked : CountedLocalCaseData.check data frame007 = true := by decide +kernel
theorem case007_fitted : fits case007 = true := by decide +kernel
noncomputable def frame008 : CountedLocalCase.Frame := {bindings := [(30, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 0, preBeta := 5439685, preBonus := 0, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 3, updateProofs := none, numericProof := 4, slack := 0}
noncomputable def case008 : PhysicalCase := ⟨0,31,.west,.walk 30,frame008⟩
theorem frame008_checked : CountedLocalCaseData.check data frame008 = true := by decide +kernel
theorem case008_fitted : fits case008 = true := by decide +kernel
noncomputable def frame009 : CountedLocalCase.Frame := {bindings := [(30, false), (56, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 0, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 3, restrictionAfterBeta := 0, restrictionAfterBonus := 11, updateProofs := none, numericProof := 3, slack := 0}
noncomputable def case009 : PhysicalCase := ⟨0,31,.southWest,.walk 56,frame009⟩
theorem frame009_checked : CountedLocalCaseData.check data frame009 = true := by decide +kernel
theorem case009_fitted : fits case009 = true := by decide +kernel
noncomputable def frame010 : CountedLocalCase.Frame := {bindings := [(29, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 2, restrictionAfterBeta := 0, restrictionAfterBonus := 2, updateProofs := none, numericProof := 0, slack := 0}
noncomputable def case010 : PhysicalCase := ⟨0,55,.north,.walk 29,frame010⟩
theorem frame010_checked : CountedLocalCaseData.check data frame010 = true := by decide +kernel
theorem case010_fitted : fits case010 = true := by decide +kernel
noncomputable def frame011 : CountedLocalCase.Frame := {bindings := [(56, false)], budget := 20, changes := [], beforeBeta := 5439685, beforeBonus := 5832765, afterBeta := 5439685, afterBonus := 5832765, preBeta := 5439685, preBonus := 5832765, restrictionBeforeBeta := 0, restrictionBeforeBonus := 12, restrictionAfterBeta := 0, restrictionAfterBonus := 12, updateProofs := none, numericProof := 5, slack := 0}
noncomputable def case011 : PhysicalCase := ⟨0,55,.east,.walk 56,frame011⟩
theorem frame011_checked : CountedLocalCaseData.check data frame011 = true := by decide +kernel
theorem case011_fitted : fits case011 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P00
