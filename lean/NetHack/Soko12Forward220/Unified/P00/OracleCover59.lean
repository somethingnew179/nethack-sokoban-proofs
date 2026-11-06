import NetHack.Soko12Forward220.Unified.P00.OracleCover58
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover708 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .northEast = some outcome) : OracleCovered rowCases708 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_east, advanceAt374_northEast, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, cornerAt374_northEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_east, advanceAt374_northEast, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, cornerAt374_northEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover709 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .northWest = some outcome) : OracleCovered rowCases709 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_west, advanceAt374_northWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_northWest, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_west, advanceAt374_northWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_northWest, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover710 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southEast = some outcome) : OracleCovered rowCases710 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_east, advanceAt374_southEast, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, cornerAt374_southEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_east, advanceAt374_southEast, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, cornerAt374_southEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover711 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southWest = some outcome) : OracleCovered rowCases711 p outcome := by
  cases h374 : p 374 with
  | false =>
    cases h400 : p 400 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southWest = some (.walk 399) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case646.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case646, memberCase646, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame646.bindings p
      intro binding member
      simp only [frame646, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h374
      · exact h400
    | true =>
      cases h373 : p 373 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southWest = some (.walk 399) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case647.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case647, memberCase647, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame647.bindings p
        intro binding member
        simp only [frame647, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h373
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 374 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover712 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .north = some outcome) : OracleCovered rowCases712 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .north = some (.walk 370) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt370_north, advanceAt370_south, advanceAt396_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case648.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case648, memberCase648, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame648.bindings p
    intro binding member
    simp only [frame648, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h370
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt370_north, advanceAt370_south, advanceAt396_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover713 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .south = some outcome) : OracleCovered rowCases713 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .south = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt422_north, advanceAt422_south, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt396_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover714 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .east = some outcome) : OracleCovered rowCases714 p outcome := by
  cases h397 : p 397 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .east = some (.walk 397) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_east, advanceAt397_east, advanceAt397_west, advanceAt398_east, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt396_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case649.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case649, memberCase649, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame649.bindings p
    intro binding member
    simp only [frame649, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h397
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_east, advanceAt397_east, advanceAt397_west, advanceAt398_east, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt396_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover715 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .west = some outcome) : OracleCovered rowCases715 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_east, advanceAt395_west, advanceAt396_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover716 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northEast = some outcome) : OracleCovered rowCases716 p outcome := by
  cases h370 : p 370 with
  | false =>
    cases h371 : p 371 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northEast = some (.walk 371) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case650.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case650, memberCase650, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame650.bindings p
      intro binding member
      simp only [frame650, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h370
      · exact h371
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    cases h397 : p 397 with
    | false =>
      cases h371 : p 371 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northEast = some (.walk 371) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case651.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case651, memberCase651, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame651.bindings p
        intro binding member
        simp only [frame651, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h371
        · exact h397
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
theorem oracleCover717 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northWest = some outcome) : OracleCovered rowCases717 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_west, advanceAt396_northWest, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover718 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .southEast = some outcome) : OracleCovered rowCases718 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt396_east, advanceAt396_southEast, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt396_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover719 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .southWest = some outcome) : OracleCovered rowCases719 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 396 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt396_west, advanceAt396_southWest, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt396_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
end NetHack.Soko12Forward220.Unified.P00
