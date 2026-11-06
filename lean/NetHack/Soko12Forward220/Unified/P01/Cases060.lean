import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame720 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 19, changes := [(169, true), (168, false)], beforeBeta := 5439691, beforeBonus := 5832798, afterBeta := 5439696, afterBonus := 5832805, preBeta := 5439687, preBonus := 0, restrictionBeforeBeta := 938337, restrictionBeforeBonus := 1336848, restrictionAfterBeta := 829, restrictionAfterBonus := 3, updateProofs := some (18552, 376003), numericProof := 75499, slack := 1}
noncomputable def case720 : PhysicalCase := ⟨1,167,.east,.push 168 (.stay 169),frame720⟩
theorem frame720_checked : CountedLocalCaseData.check data frame720 = true := by decide +kernel
theorem case720_fitted : fits case720 = true := by decide +kernel
noncomputable def frame721 : CountedLocalCase.Frame := {bindings := [(167, false), (168, true), (169, false)], budget := 19, changes := [(167, true), (168, false)], beforeBeta := 5439687, beforeBonus := 5832808, afterBeta := 5439696, afterBonus := 5832805, preBeta := 5439687, preBonus := 5833985, restrictionBeforeBeta := 829, restrictionBeforeBonus := 1336850, restrictionAfterBeta := 829, restrictionAfterBonus := 1336852, updateProofs := some (19099, 376005), numericProof := 75503, slack := 0}
noncomputable def case721 : PhysicalCase := ⟨1,169,.west,.push 168 (.stay 167),frame721⟩
theorem frame721_checked : CountedLocalCaseData.check data frame721 = true := by decide +kernel
theorem case721_fitted : fits case721 = true := by decide +kernel
noncomputable def frame722 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 19, changes := [(158, true), (184, false)], beforeBeta := 5439691, beforeBonus := 5832796, afterBeta := 5439691, afterBonus := 5832795, preBeta := 5440906, preBonus := 5833987, restrictionBeforeBeta := 16512, restrictionBeforeBonus := 1336873, restrictionAfterBeta := 941678, restrictionAfterBonus := 1336880, updateProofs := some (19818, 376024), numericProof := 75509, slack := 0}
noncomputable def case722 : PhysicalCase := ⟨1,210,.north,.push 184 (.stay 158),frame722⟩
theorem frame722_checked : CountedLocalCaseData.check data frame722 = true := by decide +kernel
theorem case722_fitted : fits case722 = true := by decide +kernel
noncomputable def frame723 : CountedLocalCase.Frame := {bindings := [(158, false), (184, true), (210, false)], budget := 19, changes := [(210, true), (184, false)], beforeBeta := 5439693, beforeBonus := 5832803, afterBeta := 5439691, afterBonus := 5832795, preBeta := 5439691, preBonus := 5833990, restrictionBeforeBeta := 2891, restrictionBeforeBonus := 1336898, restrictionAfterBeta := 16512, restrictionAfterBonus := 1336905, updateProofs := some (20869, 376043), numericProof := 75510, slack := 2}
noncomputable def case723 : PhysicalCase := ⟨1,158,.south,.push 184 (.stay 210),frame723⟩
theorem frame723_checked : CountedLocalCaseData.check data frame723 = true := by decide +kernel
theorem case723_fitted : fits case723 = true := by decide +kernel
noncomputable def frame724 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 19, changes := [(159, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832794, afterBeta := 5439691, afterBonus := 5832790, preBeta := 5440930, preBonus := 5833993, restrictionBeforeBeta := 20208, restrictionBeforeBonus := 1336926, restrictionAfterBeta := 943566, restrictionAfterBonus := 1336933, updateProofs := some (21949, 376064), numericProof := 75516, slack := 0}
noncomputable def case724 : PhysicalCase := ⟨1,211,.north,.push 185 (.stay 159),frame724⟩
theorem frame724_checked : CountedLocalCaseData.check data frame724 = true := by decide +kernel
theorem case724_fitted : fits case724 = true := by decide +kernel
noncomputable def frame725 : CountedLocalCase.Frame := {bindings := [(159, false), (185, true), (211, false)], budget := 19, changes := [(211, true), (185, false)], beforeBeta := 5439694, beforeBonus := 5832787, afterBeta := 5439691, afterBonus := 5832790, preBeta := 5439691, preBonus := 5833996, restrictionBeforeBeta := 19677, restrictionBeforeBonus := 1336947, restrictionAfterBeta := 20208, restrictionAfterBonus := 1336954, updateProofs := some (23648, 376085), numericProof := 75517, slack := 2}
noncomputable def case725 : PhysicalCase := ⟨1,159,.south,.push 185 (.stay 211),frame725⟩
theorem frame725_checked : CountedLocalCaseData.check data frame725 = true := by decide +kernel
theorem case725_fitted : fits case725 = true := by decide +kernel
noncomputable def frame726 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 19, changes := [(186, true), (185, false)], beforeBeta := 5439691, beforeBonus := 5832795, afterBeta := 5439691, afterBonus := 5832790, preBeta := 5440955, preBonus := 5833999, restrictionBeforeBeta := 79701, restrictionBeforeBonus := 1336973, restrictionAfterBeta := 946126, restrictionAfterBonus := 1336992, updateProofs := some (24871, 376106), numericProof := 75611, slack := 0}
noncomputable def case726 : PhysicalCase := ⟨1,184,.east,.push 185 (.stay 186),frame726⟩
theorem frame726_checked : CountedLocalCaseData.check data frame726 = true := by decide +kernel
theorem case726_fitted : fits case726 = true := by decide +kernel
noncomputable def frame727 : CountedLocalCase.Frame := {bindings := [(184, false), (185, true), (186, false)], budget := 19, changes := [(184, true), (185, false)], beforeBeta := 5439697, beforeBonus := 5832780, afterBeta := 5439691, afterBonus := 5832790, preBeta := 5439691, preBonus := 5834001, restrictionBeforeBeta := 80329, restrictionBeforeBonus := 1337006, restrictionAfterBeta := 79701, restrictionAfterBonus := 1337020, updateProofs := some (25998, 376127), numericProof := 75612, slack := 2}
noncomputable def case727 : PhysicalCase := ⟨1,186,.west,.push 185 (.stay 184),frame727⟩
theorem frame727_checked : CountedLocalCaseData.check data frame727 = true := by decide +kernel
theorem case727_fitted : fits case727 = true := by decide +kernel
noncomputable def frame728 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 19, changes := [(160, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832789, afterBeta := 5439697, afterBonus := 5832780, preBeta := 5440974, preBonus := 5834004, restrictionBeforeBeta := 947685, restrictionBeforeBonus := 1337034, restrictionAfterBeta := 948362, restrictionAfterBonus := 1337041, updateProofs := some (26750, 376141), numericProof := 75618, slack := 0}
noncomputable def case728 : PhysicalCase := ⟨1,212,.north,.push 186 (.stay 160),frame728⟩
theorem frame728_checked : CountedLocalCaseData.check data frame728 = true := by decide +kernel
theorem case728_fitted : fits case728 = true := by decide +kernel
noncomputable def frame729 : CountedLocalCase.Frame := {bindings := [(160, false), (186, true), (212, false)], budget := 19, changes := [(212, true), (186, false)], beforeBeta := 5439695, beforeBonus := 5832776, afterBeta := 5439697, afterBonus := 5832780, preBeta := 5440026, preBonus := 5834007, restrictionBeforeBeta := 8199, restrictionBeforeBonus := 1337061, restrictionAfterBeta := 949615, restrictionAfterBonus := 1337068, updateProofs := some (27961, 376155), numericProof := 75619, slack := 2}
noncomputable def case729 : PhysicalCase := ⟨1,160,.south,.push 186 (.stay 212),frame729⟩
theorem frame729_checked : CountedLocalCaseData.check data frame729 = true := by decide +kernel
theorem case729_fitted : fits case729 = true := by decide +kernel
noncomputable def frame730 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 19, changes := [(187, true), (186, false)], beforeBeta := 5439691, beforeBonus := 5832790, afterBeta := 5439697, afterBonus := 5832780, preBeta := 5441000, preBonus := 5834010, restrictionBeforeBeta := 949847, restrictionBeforeBonus := 1337089, restrictionAfterBeta := 951000, restrictionAfterBonus := 1337103, updateProofs := some (28839, 376169), numericProof := 75671, slack := 4}
noncomputable def case730 : PhysicalCase := ⟨1,185,.east,.push 186 (.stay 187),frame730⟩
theorem frame730_checked : CountedLocalCaseData.check data frame730 = true := by decide +kernel
theorem case730_fitted : fits case730 = true := by decide +kernel
noncomputable def frame731 : CountedLocalCase.Frame := {bindings := [(185, false), (186, true), (187, false)], budget := 19, changes := [(185, true), (186, false)], beforeBeta := 5439698, beforeBonus := 5832781, afterBeta := 5439697, afterBonus := 5832780, preBeta := 5440026, preBonus := 5834013, restrictionBeforeBeta := 951446, restrictionBeforeBonus := 1337110, restrictionAfterBeta := 952128, restrictionAfterBonus := 1337117, updateProofs := some (29636, 376183), numericProof := 75675, slack := 2}
noncomputable def case731 : PhysicalCase := ⟨1,187,.west,.push 186 (.stay 185),frame731⟩
theorem frame731_checked : CountedLocalCaseData.check data frame731 = true := by decide +kernel
theorem case731_fitted : fits case731 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
