import NetHack.Soko12Forward220.Unified.P04.OracleCover47
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover576 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .north = some outcome) : OracleCovered rowCases576 p outcome := by
  cases h288 : p 288 with
  | false =>
    cases h262 : p 262 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .north = some (.walk 262) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h262, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case536.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case536, memberCase536, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame536.bindings p
      intro binding member
      simp only [frame536, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h262
      · exact h288
    | true =>
      cases h236 : p 236 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .north = some (.push 262 (.stay 236)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h236, h262, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case808.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case808, memberCase808, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame808.bindings p
        intro binding member
        simp only [frame808, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h236
        · exact h262
        · exact h288
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h236, h262, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt2_north, advanceAt28_north, advanceAt54_north, advanceAt80_north, advanceAt106_north, advanceAt132_north, advanceAt158_north, advanceAt184_north, advanceAt210_north, advanceAt236_north, advanceAt262_north, advanceAt262_south, advanceAt288_north, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt54, doorAt54, trapAt54, boxAt54, holeAt54, floorAt80, doorAt80, trapAt80, boxAt80, holeAt80, floorAt106, doorAt106, trapAt106, boxAt106, holeAt106, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt236, doorAt236, trapAt236, boxAt236, holeAt236, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_north, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover577 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .south = some outcome) : OracleCovered rowCases577 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt314_north, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt288_south, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt314_north, advanceAt314_south, advanceAt340_south, advanceAt366_south, advanceAt392_south, advanceAt418_south, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt418, doorAt418, trapAt418, boxAt418, holeAt418, cornerAt288_south, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover578 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .east = some outcome) : OracleCovered rowCases578 p outcome := by
  cases h288 : p 288 with
  | false =>
    cases h289 : p 289 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .east = some (.walk 289) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case537.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case537, memberCase537, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame537.bindings p
      intro binding member
      simp only [frame537, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h288
      · exact h289
    | true =>
      cases h290 : p 290 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .east = some (.push 289 (.stay 290)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case826.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case826, memberCase826, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame826.bindings p
        intro binding member
        simp only [frame826, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h288
        · exact h289
        · exact h290
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_east, advanceAt289_east, advanceAt289_west, advanceAt290_east, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt288_east, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover579 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .west = some outcome) : OracleCovered rowCases579 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_east, advanceAt287_west, advanceAt288_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_west, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_east, advanceAt287_west, advanceAt288_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_west, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover580 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = some outcome) : OracleCovered rowCases580 p outcome := by
  cases h288 : p 288 with
  | false =>
    cases h262 : p 262 with
    | false =>
      cases h263 : p 263 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = some (.walk 263) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case538.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case538, memberCase538, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame538.bindings p
        intro binding member
        simp only [frame538, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h262
        · exact h263
        · exact h288
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h289 : p 289 with
      | false =>
        cases h263 : p 263 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = some (.walk 263) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case539.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case539, memberCase539, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame539.bindings p
          intro binding member
          simp only [frame539, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h263
          · exact h288
          · exact h289
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h263, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h262, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_east, advanceAt288_northEast, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt288_northEast, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover581 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northWest = some outcome) : OracleCovered rowCases581 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_west, advanceAt288_northWest, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_northWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_north, advanceAt288_west, advanceAt288_northWest, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, cornerAt288_northWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover582 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .southEast = some outcome) : OracleCovered rowCases582 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_east, advanceAt288_southEast, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, cornerAt288_southEast, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_east, advanceAt288_southEast, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, cornerAt288_southEast, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover583 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .southWest = some outcome) : OracleCovered rowCases583 p outcome := by
  cases h288 : p 288 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_west, advanceAt288_southWest, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, cornerAt288_southWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 288 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt288_south, advanceAt288_west, advanceAt288_southWest, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, cornerAt288_southWest, h288, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover584 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .north = some outcome) : OracleCovered rowCases584 p outcome := by
  cases h289 : p 289 with
  | false =>
    cases h263 : p 263 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .north = some (.walk 263) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt211_north, advanceAt237_north, advanceAt263_north, advanceAt263_south, advanceAt289_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_north, h263, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case540.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case540, memberCase540, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame540.bindings p
      intro binding member
      simp only [frame540, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h263
      · exact h289
    | true =>
      cases h237 : p 237 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .north = some (.push 263 (.stay 237)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt211_north, advanceAt237_north, advanceAt263_north, advanceAt263_south, advanceAt289_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_north, h237, h263, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case810.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case810, memberCase810, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame810.bindings p
        intro binding member
        simp only [frame810, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h237
        · exact h263
        · exact h289
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt211_north, advanceAt237_north, advanceAt263_north, advanceAt263_south, advanceAt289_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_north, h237, h263, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt159_north, advanceAt185_north, advanceAt211_north, advanceAt237_north, advanceAt263_north, advanceAt263_south, advanceAt289_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_north, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover585 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .south = some outcome) : OracleCovered rowCases585 p outcome := by
  cases h289 : p 289 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt289_south, advanceAt315_north, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt289_south, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt289_south, advanceAt315_north, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt289_south, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover586 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .east = some outcome) : OracleCovered rowCases586 p outcome := by
  cases h289 : p 289 with
  | false =>
    cases h290 : p 290 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .east = some (.walk 290) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt289_east, advanceAt290_east, advanceAt290_west, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt289_east, h289, h290, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case541.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case541, memberCase541, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame541.bindings p
      intro binding member
      simp only [frame541, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h289
      · exact h290
    | true =>
      cases h291 : p 291 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .east = some (.push 290 (.stay 291)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt289_east, advanceAt290_east, advanceAt290_west, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt289_east, h289, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case828.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case828, memberCase828, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame828.bindings p
        intro binding member
        simp only [frame828, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h289
        · exact h290
        · exact h291
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt289_east, advanceAt290_east, advanceAt290_west, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt289_east, h289, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt289_east, advanceAt290_east, advanceAt290_west, advanceAt291_east, advanceAt292_east, advanceAt293_east, advanceAt294_east, advanceAt295_east, advanceAt296_east, advanceAt297_east, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt289_east, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover587 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .west = some outcome) : OracleCovered rowCases587 p outcome := by
  cases h289 : p 289 with
  | false =>
    cases h288 : p 288 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .west = some (.walk 288) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_east, advanceAt288_west, advanceAt289_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_west, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case542.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case542, memberCase542, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame542.bindings p
      intro binding member
      simp only [frame542, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h288
      · exact h289
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_east, advanceAt288_west, advanceAt289_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_west, h288, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 289 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_east, advanceAt288_west, advanceAt289_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, cornerAt289_west, h289, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
