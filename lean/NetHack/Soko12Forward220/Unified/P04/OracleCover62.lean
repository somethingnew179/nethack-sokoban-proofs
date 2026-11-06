import NetHack.Soko12Forward220.Unified.P04.OracleCover61
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover744 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .north = some outcome) : OracleCovered rowCases744 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .north = some (.walk 370) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt370_north, advanceAt370_south, advanceAt396_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case656.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case656, memberCase656, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame656.bindings p
    intro binding member
    simp only [frame656, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h370
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt370_north, advanceAt370_south, advanceAt396_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover745 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .south = some outcome) : OracleCovered rowCases745 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .south = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt422_north, advanceAt422_south, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt396_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover746 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .east = some outcome) : OracleCovered rowCases746 p outcome := by
  cases h397 : p 397 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .east = some (.walk 397) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_east, advanceAt397_east, advanceAt397_west, advanceAt398_east, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt396_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case657.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case657, memberCase657, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame657.bindings p
    intro binding member
    simp only [frame657, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h397
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_east, advanceAt397_east, advanceAt397_west, advanceAt398_east, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt396_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover747 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .west = some outcome) : OracleCovered rowCases747 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_east, advanceAt395_west, advanceAt396_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover748 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northEast = some outcome) : OracleCovered rowCases748 p outcome := by
  cases h370 : p 370 with
  | false =>
    cases h371 : p 371 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northEast = some (.walk 371) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case658.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case658, memberCase658, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame658.bindings p
      intro binding member
      simp only [frame658, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h370
      · exact h371
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    cases h397 : p 397 with
    | false =>
      cases h371 : p 371 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northEast = some (.walk 371) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case659.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case659, memberCase659, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame659.bindings p
        intro binding member
        simp only [frame659, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h371
        · exact h397
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_east, advanceAt396_northEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt396_northEast, h370, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
theorem oracleCover749 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northWest = some outcome) : OracleCovered rowCases749 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_north, advanceAt396_west, advanceAt396_northWest, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover750 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .southEast = some outcome) : OracleCovered rowCases750 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt396_east, advanceAt396_southEast, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt396_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover751 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .southWest = some outcome) : OracleCovered rowCases751 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 396 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt396_west, advanceAt396_southWest, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt396_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover752 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .north = some outcome) : OracleCovered rowCases752 p outcome := by
  cases h397 : p 397 with
  | false =>
    cases h371 : p 371 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .north = some (.walk 371) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt371_north, advanceAt371_south, advanceAt397_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt397_north, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case660.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case660, memberCase660, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame660.bindings p
      intro binding member
      simp only [frame660, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h371
      · exact h397
    | true =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .north = some (.push 371 (.stay 345)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt371_north, advanceAt371_south, advanceAt397_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt397_north, h345, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case852.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case852, memberCase852, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame852.bindings p
        intro binding member
        simp only [frame852, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h371
        · exact h397
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt371_north, advanceAt371_south, advanceAt397_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt397_north, h345, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt371_north, advanceAt371_south, advanceAt397_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt397_north, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover753 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .south = some outcome) : OracleCovered rowCases753 p outcome := by
  cases h397 : p 397 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt397_south, advanceAt423_north, advanceAt423_south, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt397_south, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt397_south, advanceAt423_north, advanceAt423_south, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt397_south, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover754 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .east = some outcome) : OracleCovered rowCases754 p outcome := by
  cases h397 : p 397 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt397_east, advanceAt398_east, advanceAt398_west, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt397_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt397_east, advanceAt398_east, advanceAt398_west, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt397_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover755 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .west = some outcome) : OracleCovered rowCases755 p outcome := by
  cases h397 : p 397 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .west = some (.walk 396) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_west, advanceAt396_east, advanceAt396_west, advanceAt397_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt397_west, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case661.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case661, memberCase661, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame661.bindings p
    intro binding member
    simp only [frame661, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h397
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 397 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_west, advanceAt396_east, advanceAt396_west, advanceAt397_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt397_west, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
