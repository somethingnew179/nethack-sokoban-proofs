import NetHack.Soko12Forward220.Unified.P05.OracleCover57
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover696 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .north = some outcome) : OracleCovered rowCases696 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h319 : p 319 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .north = some (.walk 319) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt319_south, advanceAt345_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_north, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case624.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case624, memberCase624, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame624.bindings p
      intro binding member
      simp only [frame624, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h319
      · exact h345
    | true =>
      cases h293 : p 293 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .north = some (.push 319 (.stay 293)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt319_south, advanceAt345_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_north, h293, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case844.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case844, memberCase844, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame844.bindings p
        intro binding member
        simp only [frame844, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h293
        · exact h319
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt319_south, advanceAt345_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_north, h293, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt319_south, advanceAt345_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_north, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover697 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .south = some outcome) : OracleCovered rowCases697 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h371 : p 371 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .south = some (.walk 371) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt371_north, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt345_south, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case625.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case625, memberCase625, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame625.bindings p
      intro binding member
      simp only [frame625, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h345
      · exact h371
    | true =>
      cases h397 : p 397 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .south = some (.push 371 (.stay 397)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt371_north, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt345_south, h345, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case855.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case855, memberCase855, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame855.bindings p
        intro binding member
        simp only [frame855, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h371
        · exact h397
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt371_north, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt345_south, h345, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt371_north, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt345_south, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover698 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .east = some outcome) : OracleCovered rowCases698 p outcome := by
  cases h345 : p 345 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_east, advanceAt346_east, advanceAt346_west, advanceAt347_east, advanceAt348_east, advanceAt349_east, advanceAt350_east, advanceAt351_east, advanceAt352_east, advanceAt353_east, advanceAt354_east, advanceAt355_east, advanceAt356_east, advanceAt357_east, advanceAt358_east, advanceAt359_east, advanceAt360_east, advanceAt361_east, advanceAt362_east, advanceAt363_east, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt352, doorAt352, trapAt352, boxAt352, holeAt352, floorAt353, doorAt353, trapAt353, boxAt353, holeAt353, floorAt354, doorAt354, trapAt354, boxAt354, holeAt354, floorAt355, doorAt355, trapAt355, boxAt355, holeAt355, floorAt356, doorAt356, trapAt356, boxAt356, holeAt356, floorAt357, doorAt357, trapAt357, boxAt357, holeAt357, floorAt358, doorAt358, trapAt358, boxAt358, holeAt358, floorAt359, doorAt359, trapAt359, boxAt359, holeAt359, floorAt360, doorAt360, trapAt360, boxAt360, holeAt360, floorAt361, doorAt361, trapAt361, boxAt361, holeAt361, floorAt362, doorAt362, trapAt362, boxAt362, holeAt362, floorAt363, doorAt363, trapAt363, boxAt363, holeAt363, cornerAt345_east, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_east, advanceAt346_east, advanceAt346_west, advanceAt347_east, advanceAt348_east, advanceAt349_east, advanceAt350_east, advanceAt351_east, advanceAt352_east, advanceAt353_east, advanceAt354_east, advanceAt355_east, advanceAt356_east, advanceAt357_east, advanceAt358_east, advanceAt359_east, advanceAt360_east, advanceAt361_east, advanceAt362_east, advanceAt363_east, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt352, doorAt352, trapAt352, boxAt352, holeAt352, floorAt353, doorAt353, trapAt353, boxAt353, holeAt353, floorAt354, doorAt354, trapAt354, boxAt354, holeAt354, floorAt355, doorAt355, trapAt355, boxAt355, holeAt355, floorAt356, doorAt356, trapAt356, boxAt356, holeAt356, floorAt357, doorAt357, trapAt357, boxAt357, holeAt357, floorAt358, doorAt358, trapAt358, boxAt358, holeAt358, floorAt359, doorAt359, trapAt359, boxAt359, holeAt359, floorAt360, doorAt360, trapAt360, boxAt360, holeAt360, floorAt361, doorAt361, trapAt361, boxAt361, holeAt361, floorAt362, doorAt362, trapAt362, boxAt362, holeAt362, floorAt363, doorAt363, trapAt363, boxAt363, holeAt363, cornerAt345_east, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover699 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .west = some outcome) : OracleCovered rowCases699 p outcome := by
  cases h345 : p 345 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt338_west, advanceAt339_west, advanceAt340_west, advanceAt341_west, advanceAt342_west, advanceAt343_west, advanceAt344_east, advanceAt344_west, advanceAt345_west, floorAt338, doorAt338, trapAt338, boxAt338, holeAt338, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_west, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt338_west, advanceAt339_west, advanceAt340_west, advanceAt341_west, advanceAt342_west, advanceAt343_west, advanceAt344_east, advanceAt344_west, advanceAt345_west, floorAt338, doorAt338, trapAt338, boxAt338, holeAt338, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_west, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover700 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northEast = some outcome) : OracleCovered rowCases700 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h320 : p 320 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northEast = some (.walk 320) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case626.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case626, memberCase626, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame626.bindings p
        intro binding member
        simp only [frame626, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h319
        · exact h320
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover701 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northWest = some outcome) : OracleCovered rowCases701 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h318 : p 318 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northWest = some (.walk 318) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h318, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case627.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case627, memberCase627, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame627.bindings p
        intro binding member
        simp only [frame627, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h318
        · exact h319
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h318, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover702 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southEast = some outcome) : OracleCovered rowCases702 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h372 : p 372 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southEast = some (.walk 372) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case628.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case628, memberCase628, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame628.bindings p
        intro binding member
        simp only [frame628, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h371
        · exact h372
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover703 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southWest = some outcome) : OracleCovered rowCases703 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h370 : p 370 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southWest = some (.walk 370) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case629.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case629, memberCase629, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame629.bindings p
        intro binding member
        simp only [frame629, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h370
        · exact h371
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 345 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover704 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .north = some outcome) : OracleCovered rowCases704 p outcome := by
  cases h348 : p 348 with
  | false =>
    cases h322 : p 322 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .north = some (.walk 322) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case630.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case630, memberCase630, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame630.bindings p
      intro binding member
      simp only [frame630, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h322
      · exact h348
    | true =>
      cases h296 : p 296 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .north = some (.push 322 (.stay 296)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case848.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case848, memberCase848, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame848.bindings p
        intro binding member
        simp only [frame848, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h296
        · exact h322
        · exact h348
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover705 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .south = some outcome) : OracleCovered rowCases705 p outcome := by
  cases h348 : p 348 with
  | false =>
    cases h374 : p 374 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .south = some (.walk 374) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case631.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case631, memberCase631, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame631.bindings p
      intro binding member
      simp only [frame631, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h348
      · exact h374
    | true =>
      cases h400 : p 400 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .south = some (.push 374 (.stay 400)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case863.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case863, memberCase863, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame863.bindings p
        intro binding member
        simp only [frame863, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h348
        · exact h374
        · exact h400
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover706 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .east = some outcome) : OracleCovered rowCases706 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_east, advanceAt349_east, advanceAt349_west, advanceAt350_east, advanceAt351_east, advanceAt352_east, advanceAt353_east, advanceAt354_east, advanceAt355_east, advanceAt356_east, advanceAt357_east, advanceAt358_east, advanceAt359_east, advanceAt360_east, advanceAt361_east, advanceAt362_east, advanceAt363_east, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt352, doorAt352, trapAt352, boxAt352, holeAt352, floorAt353, doorAt353, trapAt353, boxAt353, holeAt353, floorAt354, doorAt354, trapAt354, boxAt354, holeAt354, floorAt355, doorAt355, trapAt355, boxAt355, holeAt355, floorAt356, doorAt356, trapAt356, boxAt356, holeAt356, floorAt357, doorAt357, trapAt357, boxAt357, holeAt357, floorAt358, doorAt358, trapAt358, boxAt358, holeAt358, floorAt359, doorAt359, trapAt359, boxAt359, holeAt359, floorAt360, doorAt360, trapAt360, boxAt360, holeAt360, floorAt361, doorAt361, trapAt361, boxAt361, holeAt361, floorAt362, doorAt362, trapAt362, boxAt362, holeAt362, floorAt363, doorAt363, trapAt363, boxAt363, holeAt363, cornerAt348_east, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_east, advanceAt349_east, advanceAt349_west, advanceAt350_east, advanceAt351_east, advanceAt352_east, advanceAt353_east, advanceAt354_east, advanceAt355_east, advanceAt356_east, advanceAt357_east, advanceAt358_east, advanceAt359_east, advanceAt360_east, advanceAt361_east, advanceAt362_east, advanceAt363_east, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt352, doorAt352, trapAt352, boxAt352, holeAt352, floorAt353, doorAt353, trapAt353, boxAt353, holeAt353, floorAt354, doorAt354, trapAt354, boxAt354, holeAt354, floorAt355, doorAt355, trapAt355, boxAt355, holeAt355, floorAt356, doorAt356, trapAt356, boxAt356, holeAt356, floorAt357, doorAt357, trapAt357, boxAt357, holeAt357, floorAt358, doorAt358, trapAt358, boxAt358, holeAt358, floorAt359, doorAt359, trapAt359, boxAt359, holeAt359, floorAt360, doorAt360, trapAt360, boxAt360, holeAt360, floorAt361, doorAt361, trapAt361, boxAt361, holeAt361, floorAt362, doorAt362, trapAt362, boxAt362, holeAt362, floorAt363, doorAt363, trapAt363, boxAt363, holeAt363, cornerAt348_east, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover707 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .west = some outcome) : OracleCovered rowCases707 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt338_west, advanceAt339_west, advanceAt340_west, advanceAt341_west, advanceAt342_west, advanceAt343_west, advanceAt344_west, advanceAt345_west, advanceAt346_west, advanceAt347_east, advanceAt347_west, advanceAt348_west, floorAt338, doorAt338, trapAt338, boxAt338, holeAt338, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_west, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 348 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt338_west, advanceAt339_west, advanceAt340_west, advanceAt341_west, advanceAt342_west, advanceAt343_west, advanceAt344_west, advanceAt345_west, advanceAt346_west, advanceAt347_east, advanceAt347_west, advanceAt348_west, floorAt338, doorAt338, trapAt338, boxAt338, holeAt338, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_west, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P05
