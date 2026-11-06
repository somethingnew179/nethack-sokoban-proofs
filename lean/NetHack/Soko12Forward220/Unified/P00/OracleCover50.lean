import NetHack.Soko12Forward220.Unified.P00.OracleCover49
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover600 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .north = some outcome) : OracleCovered rowCases600 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h270 : p 270 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .north = some (.walk 270) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case574.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case574, memberCase574, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame574.bindings p
      intro binding member
      simp only [frame574, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h270
      · exact h296
    | true =>
      cases h244 : p 244 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .north = some (.push 270 (.stay 244)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h244, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case812.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case812, memberCase812, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame812.bindings p
        intro binding member
        simp only [frame812, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h244
        · exact h270
        · exact h296
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h244, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt270_south, advanceAt296_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_north, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover601 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .south = some outcome) : OracleCovered rowCases601 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h322 : p 322 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .south = some (.walk 322) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case575.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case575, memberCase575, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame575.bindings p
      intro binding member
      simp only [frame575, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h322
    | true =>
      cases h348 : p 348 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .south = some (.push 322 (.stay 348)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case839.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case839, memberCase839, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame839.bindings p
        intro binding member
        simp only [frame839, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h296
        · exact h322
        · exact h348
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt322_north, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt296_south, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover602 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .east = some outcome) : OracleCovered rowCases602 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h297 : p 297 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .east = some (.walk 297) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_east, advanceAt297_east, advanceAt297_west, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt296_east, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case576.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case576, memberCase576, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame576.bindings p
      intro binding member
      simp only [frame576, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h297
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_east, advanceAt297_east, advanceAt297_west, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt296_east, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_east, advanceAt297_east, advanceAt297_west, advanceAt298_east, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt296_east, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover603 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .west = some outcome) : OracleCovered rowCases603 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_east, advanceAt295_west, advanceAt296_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_west, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_east, advanceAt295_west, advanceAt296_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_west, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover604 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = some outcome) : OracleCovered rowCases604 p outcome := by
  cases h296 : p 296 with
  | false =>
    cases h270 : p 270 with
    | false =>
      cases h271 : p 271 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = some (.walk 271) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case577.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case577, memberCase577, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame577.bindings p
        intro binding member
        simp only [frame577, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h271
        · exact h296
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h297 : p 297 with
      | false =>
        cases h271 : p 271 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = some (.walk 271) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case578.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case578, memberCase578, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame578.bindings p
          intro binding member
          simp only [frame578, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h271
          · exact h296
          · exact h297
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h270, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_east, advanceAt296_northEast, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt296_northEast, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover605 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northWest = some outcome) : OracleCovered rowCases605 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_west, advanceAt296_northWest, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_northWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_north, advanceAt296_west, advanceAt296_northWest, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, cornerAt296_northWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover606 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .southEast = some outcome) : OracleCovered rowCases606 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_east, advanceAt296_southEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt296_southEast, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_east, advanceAt296_southEast, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt296_southEast, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover607 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .southWest = some outcome) : OracleCovered rowCases607 p outcome := by
  cases h296 : p 296 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_west, advanceAt296_southWest, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt296_southWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 296 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt296_south, advanceAt296_west, advanceAt296_southWest, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt296_southWest, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover608 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .north = some outcome) : OracleCovered rowCases608 p outcome := by
  cases h297 : p 297 with
  | false =>
    cases h271 : p 271 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .north = some (.walk 271) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt245_north, advanceAt271_north, advanceAt271_south, advanceAt297_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_north, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case579.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case579, memberCase579, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame579.bindings p
      intro binding member
      simp only [frame579, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h271
      · exact h297
    | true =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .north = some (.push 271 (.stay 245)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt245_north, advanceAt271_north, advanceAt271_south, advanceAt297_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_north, h245, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case814.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case814, memberCase814, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame814.bindings p
        intro binding member
        simp only [frame814, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h245
        · exact h271
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt245_north, advanceAt271_north, advanceAt271_south, advanceAt297_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_north, h245, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt219_north, advanceAt245_north, advanceAt271_north, advanceAt271_south, advanceAt297_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_north, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover609 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .south = some outcome) : OracleCovered rowCases609 p outcome := by
  cases h297 : p 297 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt323_north, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt297_south, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt323_north, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt297_south, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover610 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .east = some outcome) : OracleCovered rowCases610 p outcome := by
  cases h297 : p 297 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_east, advanceAt298_east, advanceAt298_west, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt297_east, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_east, advanceAt298_east, advanceAt298_west, advanceAt299_east, advanceAt300_east, advanceAt301_east, advanceAt302_east, advanceAt303_east, advanceAt304_east, advanceAt305_east, advanceAt306_east, advanceAt307_east, advanceAt308_east, advanceAt309_east, advanceAt310_east, advanceAt311_east, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt299, doorAt299, trapAt299, boxAt299, holeAt299, floorAt300, doorAt300, trapAt300, boxAt300, holeAt300, floorAt301, doorAt301, trapAt301, boxAt301, holeAt301, floorAt302, doorAt302, trapAt302, boxAt302, holeAt302, floorAt303, doorAt303, trapAt303, boxAt303, holeAt303, floorAt304, doorAt304, trapAt304, boxAt304, holeAt304, floorAt305, doorAt305, trapAt305, boxAt305, holeAt305, floorAt306, doorAt306, trapAt306, boxAt306, holeAt306, floorAt307, doorAt307, trapAt307, boxAt307, holeAt307, floorAt308, doorAt308, trapAt308, boxAt308, holeAt308, floorAt309, doorAt309, trapAt309, boxAt309, holeAt309, floorAt310, doorAt310, trapAt310, boxAt310, holeAt310, floorAt311, doorAt311, trapAt311, boxAt311, holeAt311, cornerAt297_east, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover611 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .west = some outcome) : OracleCovered rowCases611 p outcome := by
  cases h297 : p 297 with
  | false =>
    cases h296 : p 296 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .west = some (.walk 296) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_west, advanceAt296_east, advanceAt296_west, advanceAt297_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_west, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case580.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case580, memberCase580, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame580.bindings p
      intro binding member
      simp only [frame580, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h297
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_west, advanceAt296_east, advanceAt296_west, advanceAt297_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_west, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt286_west, advanceAt287_west, advanceAt288_west, advanceAt289_west, advanceAt290_west, advanceAt291_west, advanceAt292_west, advanceAt293_west, advanceAt294_west, advanceAt295_west, advanceAt296_east, advanceAt296_west, advanceAt297_west, floorAt286, doorAt286, trapAt286, boxAt286, holeAt286, floorAt287, doorAt287, trapAt287, boxAt287, holeAt287, floorAt288, doorAt288, trapAt288, boxAt288, holeAt288, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_west, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
