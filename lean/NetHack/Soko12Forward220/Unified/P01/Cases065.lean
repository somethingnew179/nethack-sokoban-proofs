import NetHack.Soko12Forward220.Unified.P01.CaseData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban
noncomputable def frame780 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 19, changes := [(194, true), (220, false)], beforeBeta := 5439691, beforeBonus := 0, afterBeta := 5439691, afterBonus := 5832804, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 3, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (131971, 376453), numericProof := 75790, slack := 1}
noncomputable def case780 : PhysicalCase := ⟨1,246,.north,.push 220 (.stay 194),frame780⟩
theorem frame780_checked : CountedLocalCaseData.check data frame780 = true := by decide +kernel
theorem case780_fitted : fits case780 = true := by decide +kernel
noncomputable def frame781 : CountedLocalCase.Frame := {bindings := [(194, false), (220, true), (246, false)], budget := 19, changes := [(246, true), (220, false)], beforeBeta := 5439691, beforeBonus := 5832804, afterBeta := 5439691, afterBonus := 5832804, preBeta := 5439691, preBonus := 5834102, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337530, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337532, updateProofs := some (137164, 376455), numericProof := 75791, slack := 1}
noncomputable def case781 : PhysicalCase := ⟨1,194,.south,.push 220 (.stay 246),frame781⟩
theorem frame781_checked : CountedLocalCaseData.check data frame781 = true := by decide +kernel
theorem case781_fitted : fits case781 = true := by decide +kernel
noncomputable def frame782 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 19, changes := [(210, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 5834104, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337553, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337560, updateProofs := some (138557, 376476), numericProof := 75792, slack := 0}
noncomputable def case782 : PhysicalCase := ⟨1,262,.north,.push 236 (.stay 210),frame782⟩
theorem frame782_checked : CountedLocalCaseData.check data frame782 = true := by decide +kernel
theorem case782_fitted : fits case782 = true := by decide +kernel
noncomputable def frame783 : CountedLocalCase.Frame := {bindings := [(210, false), (236, true), (262, false)], budget := 19, changes := [(262, true), (236, false)], beforeBeta := 5439691, beforeBonus := 5832796, afterBeta := 5439691, afterBonus := 5832802, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337574, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (140071, 376497), numericProof := 75793, slack := 2}
noncomputable def case783 : PhysicalCase := ⟨1,210,.south,.push 236 (.stay 262),frame783⟩
theorem frame783_checked : CountedLocalCaseData.check data frame783 = true := by decide +kernel
theorem case783_fitted : fits case783 = true := by decide +kernel
noncomputable def frame784 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 19, changes := [(211, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832812, afterBeta := 5439691, afterBonus := 5832813, preBeta := 5439691, preBonus := 5834106, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337595, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337602, updateProofs := some (141440, 376518), numericProof := 75794, slack := 0}
noncomputable def case784 : PhysicalCase := ⟨1,263,.north,.push 237 (.stay 211),frame784⟩
theorem frame784_checked : CountedLocalCaseData.check data frame784 = true := by decide +kernel
theorem case784_fitted : fits case784 = true := by decide +kernel
noncomputable def frame785 : CountedLocalCase.Frame := {bindings := [(211, false), (237, true), (263, false)], budget := 19, changes := [(263, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832794, afterBeta := 5439691, afterBonus := 5832813, preBeta := 5439691, preBonus := 5834108, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337616, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337623, updateProofs := some (142896, 376539), numericProof := 75795, slack := 2}
noncomputable def case785 : PhysicalCase := ⟨1,211,.south,.push 237 (.stay 263),frame785⟩
theorem frame785_checked : CountedLocalCaseData.check data frame785 = true := by decide +kernel
theorem case785_fitted : fits case785 = true := by decide +kernel
noncomputable def frame786 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 19, changes := [(238, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832802, afterBeta := 5439691, afterBonus := 5832813, preBeta := 5439691, preBonus := 5834111, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337644, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337663, updateProofs := some (144294, 376560), numericProof := 75813, slack := 0}
noncomputable def case786 : PhysicalCase := ⟨1,236,.east,.push 237 (.stay 238),frame786⟩
theorem frame786_checked : CountedLocalCaseData.check data frame786 = true := by decide +kernel
theorem case786_fitted : fits case786 = true := by decide +kernel
noncomputable def frame787 : CountedLocalCase.Frame := {bindings := [(236, false), (237, true), (238, false)], budget := 19, changes := [(236, true), (237, false)], beforeBeta := 5439691, beforeBonus := 5832818, afterBeta := 5439691, afterBonus := 5832813, preBeta := 5439691, preBonus := 0, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337676, restrictionAfterBeta := 8531, restrictionAfterBonus := 3, updateProofs := some (145671, 376581), numericProof := 75814, slack := 2}
noncomputable def case787 : PhysicalCase := ⟨1,238,.west,.push 237 (.stay 236),frame787⟩
theorem frame787_checked : CountedLocalCaseData.check data frame787 = true := by decide +kernel
theorem case787_fitted : fits case787 = true := by decide +kernel
noncomputable def frame788 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 19, changes := [(212, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832815, afterBeta := 5439691, afterBonus := 5832818, preBeta := 5439691, preBonus := 5834115, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337697, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337704, updateProofs := some (146345, 376595), numericProof := 75815, slack := 0}
noncomputable def case788 : PhysicalCase := ⟨1,264,.north,.push 238 (.stay 212),frame788⟩
theorem frame788_checked : CountedLocalCaseData.check data frame788 = true := by decide +kernel
theorem case788_fitted : fits case788 = true := by decide +kernel
noncomputable def frame789 : CountedLocalCase.Frame := {bindings := [(212, false), (238, true), (264, false)], budget := 19, changes := [(264, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832789, afterBeta := 5439691, afterBonus := 5832818, preBeta := 5439691, preBonus := 5834117, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337717, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337724, updateProofs := some (147122, 376609), numericProof := 75816, slack := 2}
noncomputable def case789 : PhysicalCase := ⟨1,212,.south,.push 238 (.stay 264),frame789⟩
theorem frame789_checked : CountedLocalCaseData.check data frame789 = true := by decide +kernel
theorem case789_fitted : fits case789 = true := by decide +kernel
noncomputable def frame790 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 19, changes := [(239, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832813, afterBeta := 5439691, afterBonus := 5832818, preBeta := 5439691, preBonus := 5834120, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337745, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337759, updateProofs := some (147813, 376623), numericProof := 75817, slack := 2}
noncomputable def case790 : PhysicalCase := ⟨1,237,.east,.push 238 (.stay 239),frame790⟩
theorem frame790_checked : CountedLocalCaseData.check data frame790 = true := by decide +kernel
theorem case790_fitted : fits case790 = true := by decide +kernel
noncomputable def frame791 : CountedLocalCase.Frame := {bindings := [(237, false), (238, true), (239, false)], budget := 19, changes := [(237, true), (238, false)], beforeBeta := 5439691, beforeBonus := 5832784, afterBeta := 5439691, afterBonus := 5832818, preBeta := 5439691, preBonus := 5834123, restrictionBeforeBeta := 8531, restrictionBeforeBonus := 1337773, restrictionAfterBeta := 8531, restrictionAfterBonus := 1337780, updateProofs := some (148494, 376637), numericProof := 75818, slack := 2}
noncomputable def case791 : PhysicalCase := ⟨1,239,.west,.push 238 (.stay 237),frame791⟩
theorem frame791_checked : CountedLocalCaseData.check data frame791 = true := by decide +kernel
theorem case791_fitted : fits case791 = true := by decide +kernel
end NetHack.Soko12Forward220.Unified.P01
