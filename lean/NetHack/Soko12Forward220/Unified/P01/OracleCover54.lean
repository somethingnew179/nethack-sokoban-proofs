import NetHack.Soko12Forward220.Unified.P01.OracleCover53
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover648 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .north = some outcome) : OracleCovered rowCases648 p outcome := by
  cases h320 : p 320 with
  | false =>
    cases h294 : p 294 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .north = some (.walk 294) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt242_north, advanceAt268_north, advanceAt294_north, advanceAt294_south, advanceAt320_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_north, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case608.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case608, memberCase608, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame608.bindings p
      intro binding member
      simp only [frame608, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h294
      · exact h320
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt242_north, advanceAt268_north, advanceAt294_north, advanceAt294_south, advanceAt320_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_north, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt242_north, advanceAt268_north, advanceAt294_north, advanceAt294_south, advanceAt320_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_north, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover649 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .south = some outcome) : OracleCovered rowCases649 p outcome := by
  cases h320 : p 320 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt346_north, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt320_south, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt346_north, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt320_south, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover650 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .east = some outcome) : OracleCovered rowCases650 p outcome := by
  cases h320 : p 320 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_east, advanceAt321_east, advanceAt321_west, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt320_east, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_east, advanceAt321_east, advanceAt321_west, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt320_east, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover651 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .west = some outcome) : OracleCovered rowCases651 p outcome := by
  cases h320 : p 320 with
  | false =>
    cases h319 : p 319 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .west = some (.walk 319) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_east, advanceAt319_west, advanceAt320_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_west, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case609.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case609, memberCase609, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame609.bindings p
      intro binding member
      simp only [frame609, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h319
      · exact h320
    | true =>
      cases h318 : p 318 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .west = some (.push 319 (.stay 318)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_east, advanceAt319_west, advanceAt320_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_west, h318, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case839.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case839, memberCase839, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame839.bindings p
        intro binding member
        simp only [frame839, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h318
        · exact h319
        · exact h320
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_east, advanceAt319_west, advanceAt320_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_west, h318, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_east, advanceAt319_west, advanceAt320_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_west, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover652 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northEast = some outcome) : OracleCovered rowCases652 p outcome := by
  cases h320 : p 320 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_east, advanceAt320_northEast, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, cornerAt320_northEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_east, advanceAt320_northEast, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, cornerAt320_northEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover653 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = some outcome) : OracleCovered rowCases653 p outcome := by
  cases h320 : p 320 with
  | false =>
    cases h294 : p 294 with
    | false =>
      cases h293 : p 293 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = some (.walk 293) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case610.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case610, memberCase610, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame610.bindings p
        intro binding member
        simp only [frame610, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h293
        · exact h294
        · exact h320
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h319 : p 319 with
      | false =>
        cases h293 : p 293 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = some (.walk 293) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case611.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case611, memberCase611, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame611.bindings p
          intro binding member
          simp only [frame611, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h293
          · exact h319
          · exact h320
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h293, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h294, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_north, advanceAt320_west, advanceAt320_northWest, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, cornerAt320_northWest, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover654 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southEast = some outcome) : OracleCovered rowCases654 p outcome := by
  cases h320 : p 320 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_east, advanceAt320_southEast, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, cornerAt320_southEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_east, advanceAt320_southEast, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, cornerAt320_southEast, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover655 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southWest = some outcome) : OracleCovered rowCases655 p outcome := by
  cases h320 : p 320 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southWest = some (.walk 345) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case612.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case612, memberCase612, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame612.bindings p
        intro binding member
        simp only [frame612, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h319
        · exact h320
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h319, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 320 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt320_south, advanceAt320_west, advanceAt320_southWest, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt320_southWest, h320, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover656 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .north = some outcome) : OracleCovered rowCases656 p outcome := by
  cases h322 : p 322 with
  | false =>
    cases h296 : p 296 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .north = some (.walk 296) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case613.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case613, memberCase613, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame613.bindings p
      intro binding member
      simp only [frame613, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h296
      · exact h322
    | true =>
      cases h270 : p 270 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .north = some (.push 296 (.stay 270)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h270, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case832.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case832, memberCase832, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame832.bindings p
        intro binding member
        simp only [frame832, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h296
        · exact h322
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h270, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt296_south, advanceAt322_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_north, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover657 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .south = some outcome) : OracleCovered rowCases657 p outcome := by
  cases h322 : p 322 with
  | false =>
    cases h348 : p 348 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .south = some (.walk 348) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case614.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case614, memberCase614, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame614.bindings p
      intro binding member
      simp only [frame614, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h322
      · exact h348
    | true =>
      cases h374 : p 374 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .south = some (.push 348 (.stay 374)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case845.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case845, memberCase845, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame845.bindings p
        intro binding member
        simp only [frame845, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h322
        · exact h348
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_south, advanceAt348_north, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt322_south, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover658 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .east = some outcome) : OracleCovered rowCases658 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_east, advanceAt323_east, advanceAt323_west, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt322_east, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt322_east, advanceAt323_east, advanceAt323_west, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt322_east, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover659 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .west = some outcome) : OracleCovered rowCases659 p outcome := by
  cases h322 : p 322 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_west, advanceAt320_west, advanceAt321_east, advanceAt321_west, advanceAt322_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_west, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 322 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_west, advanceAt317_west, advanceAt318_west, advanceAt319_west, advanceAt320_west, advanceAt321_east, advanceAt321_west, advanceAt322_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, cornerAt322_west, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
