import NetHack.Soko12Forward220.Unified.P05.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban
noncomputable def frame840 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 15, changes := [(270, true), (296, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (262583, 257920), numericProof := 78301, slack := 1}
noncomputable def case840 : PhysicalCase := ⟨5,322,.north,.push 296 (.stay 270),frame840⟩
theorem frame840_checked : CountedLocalCaseData.check data frame840 = true := by decide +kernel
theorem case840_fitted : fits case840 = true := by decide +kernel
noncomputable def frame841 : CountedLocalCase.Frame := {bindings := [(270, false), (296, true), (322, false)], budget := 15, changes := [(322, true), (296, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (267420, 262584), numericProof := 78301, slack := 1}
noncomputable def case841 : PhysicalCase := ⟨5,270,.south,.push 296 (.stay 322),frame841⟩
theorem frame841_checked : CountedLocalCaseData.check data frame841 = true := by decide +kernel
theorem case841_fitted : fits case841 = true := by decide +kernel
noncomputable def frame842 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 15, changes := [(319, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832915, preBeta := 5439691, preBonus := 5835269, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345210, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345212, updateProofs := some (269156, 379081), numericProof := 78302, slack := 0}
noncomputable def case842 : PhysicalCase := ⟨5,317,.east,.push 318 (.stay 319),frame842⟩
theorem frame842_checked : CountedLocalCaseData.check data frame842 = true := by decide +kernel
theorem case842_fitted : fits case842 = true := by decide +kernel
noncomputable def frame843 : CountedLocalCase.Frame := {bindings := [(317, false), (318, true), (319, false)], budget := 15, changes := [(317, true), (318, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832915, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345214, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (270886, 379083), numericProof := 78303, slack := 3}
noncomputable def case843 : PhysicalCase := ⟨5,319,.west,.push 318 (.stay 317),frame843⟩
theorem frame843_checked : CountedLocalCaseData.check data frame843 = true := by decide +kernel
theorem case843_fitted : fits case843 = true := by decide +kernel
noncomputable def frame844 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 15, changes := [(293, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345216, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (276451, 379085), numericProof := 78304, slack := 0}
noncomputable def case844 : PhysicalCase := ⟨5,345,.north,.push 319 (.stay 293),frame844⟩
theorem frame844_checked : CountedLocalCaseData.check data frame844 = true := by decide +kernel
theorem case844_fitted : fits case844 = true := by decide +kernel
noncomputable def frame845 : CountedLocalCase.Frame := {bindings := [(293, false), (319, true), (345, false)], budget := 15, changes := [(345, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345218, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (282031, 379087), numericProof := 78305, slack := 2}
noncomputable def case845 : PhysicalCase := ⟨5,293,.south,.push 319 (.stay 345),frame845⟩
theorem frame845_checked : CountedLocalCaseData.check data frame845 = true := by decide +kernel
theorem case845_fitted : fits case845 = true := by decide +kernel
noncomputable def frame846 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 15, changes := [(320, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832915, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345220, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (287603, 379089), numericProof := 78306, slack := 4}
noncomputable def case846 : PhysicalCase := ⟨5,318,.east,.push 319 (.stay 320),frame846⟩
theorem frame846_checked : CountedLocalCaseData.check data frame846 = true := by decide +kernel
theorem case846_fitted : fits case846 = true := by decide +kernel
noncomputable def frame847 : CountedLocalCase.Frame := {bindings := [(318, false), (319, true), (320, false)], budget := 15, changes := [(318, true), (319, false)], beforeBeta := 5439691, beforeBonus := 5832909, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 5835269, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345222, restrictionAfterBeta := 8531, restrictionAfterBonus := 1345224, updateProofs := some (293175, 379091), numericProof := 78307, slack := 2}
noncomputable def case847 : PhysicalCase := ⟨5,320,.west,.push 319 (.stay 318),frame847⟩
theorem frame847_checked : CountedLocalCaseData.check data frame847 = true := by decide +kernel
theorem case847_fitted : fits case847 = true := by decide +kernel
noncomputable def frame848 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 15, changes := [(296, true), (322, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (297970, 293176), numericProof := 78308, slack := 1}
noncomputable def case848 : PhysicalCase := ⟨5,348,.north,.push 322 (.stay 296),frame848⟩
theorem frame848_checked : CountedLocalCaseData.check data frame848 = true := by decide +kernel
theorem case848_fitted : fits case848 = true := by decide +kernel
noncomputable def frame849 : CountedLocalCase.Frame := {bindings := [(296, false), (322, true), (348, false)], budget := 15, changes := [(348, true), (322, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 0, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (302816, 297971), numericProof := 78308, slack := 1}
noncomputable def case849 : PhysicalCase := ⟨5,296,.south,.push 322 (.stay 348),frame849⟩
theorem frame849_checked : CountedLocalCaseData.check data frame849 = true := by decide +kernel
theorem case849_fitted : fits case849 = true := by decide +kernel
noncomputable def frame850 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 15, changes := [(319, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345226, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (308429, 379093), numericProof := 78309, slack := 0}
noncomputable def case850 : PhysicalCase := ⟨5,371,.north,.push 345 (.stay 319),frame850⟩
theorem frame850_checked : CountedLocalCaseData.check data frame850 = true := by decide +kernel
theorem case850_fitted : fits case850 = true := by decide +kernel
noncomputable def frame851 : CountedLocalCase.Frame := {bindings := [(319, false), (345, true), (371, false)], budget := 15, changes := [(371, true), (345, false)], beforeBeta := 5439691, beforeBonus := 5832914, afterBeta := 5439691, afterBonus := 5832914, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1345226, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (314054, 379095), numericProof := 78310, slack := 2}
noncomputable def case851 : PhysicalCase := ⟨5,319,.south,.push 345 (.stay 371),frame851⟩
theorem frame851_checked : CountedLocalCaseData.check data frame851 = true := by decide +kernel
theorem case851_fitted : fits case851 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P05
