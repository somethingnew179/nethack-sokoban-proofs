import NetHack.Soko12Forward220.Unified.P01.OracleCover17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover216 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .north = some outcome) : OracleCovered rowCases216 p outcome := by
  cases h163 : p 163 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt137_south, advanceAt163_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, cornerAt163_north, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt137_south, advanceAt163_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, cornerAt163_north, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover217 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .south = some outcome) : OracleCovered rowCases217 p outcome := by
  cases h163 : p 163 with
  | false =>
    cases h189 : p 189 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .south = some (.walk 189) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt189_north, advanceAt189_south, advanceAt215_south, advanceAt241_south, advanceAt267_south, advanceAt293_south, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt163_south, h163, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case173.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case173, memberCase173, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame173.bindings p
      intro binding member
      simp only [frame173, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h163
      · exact h189
    | true =>
      cases h215 : p 215 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .south = some (.push 189 (.stay 215)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt189_north, advanceAt189_south, advanceAt215_south, advanceAt241_south, advanceAt267_south, advanceAt293_south, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt163_south, h163, h189, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case735.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case735, memberCase735, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame735.bindings p
        intro binding member
        simp only [frame735, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h163
        · exact h189
        · exact h215
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt189_north, advanceAt189_south, advanceAt215_south, advanceAt241_south, advanceAt267_south, advanceAt293_south, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt163_south, h163, h189, h215, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt189_north, advanceAt189_south, advanceAt215_south, advanceAt241_south, advanceAt267_south, advanceAt293_south, advanceAt319_south, advanceAt345_south, advanceAt371_south, advanceAt397_south, advanceAt423_south, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt163_south, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover218 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .east = some outcome) : OracleCovered rowCases218 p outcome := by
  cases h163 : p 163 with
  | false =>
    cases h164 : p 164 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .east = some (.walk 164) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_east, advanceAt164_east, advanceAt164_west, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt163_east, h163, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case174.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case174, memberCase174, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame174.bindings p
      intro binding member
      simp only [frame174, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h163
      · exact h164
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_east, advanceAt164_east, advanceAt164_west, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt163_east, h163, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_east, advanceAt164_east, advanceAt164_west, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt163_east, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover219 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .west = some outcome) : OracleCovered rowCases219 p outcome := by
  cases h163 : p 163 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_east, advanceAt162_west, advanceAt163_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, cornerAt163_west, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_east, advanceAt162_west, advanceAt163_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, cornerAt163_west, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover220 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .northEast = some outcome) : OracleCovered rowCases220 p outcome := by
  cases h163 : p 163 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_north, advanceAt163_east, advanceAt163_northEast, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt163_northEast, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_north, advanceAt163_east, advanceAt163_northEast, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt163_northEast, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover221 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .northWest = some outcome) : OracleCovered rowCases221 p outcome := by
  cases h163 : p 163 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_north, advanceAt163_west, advanceAt163_northWest, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, cornerAt163_northWest, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_north, advanceAt163_west, advanceAt163_northWest, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, cornerAt163_northWest, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover222 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = some outcome) : OracleCovered rowCases222 p outcome := by
  cases h163 : p 163 with
  | false =>
    cases h189 : p 189 with
    | false =>
      cases h190 : p 190 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = some (.walk 190) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_east, advanceAt163_southEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt163_southEast, h163, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case175.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case175, memberCase175, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame175.bindings p
        intro binding member
        simp only [frame175, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h163
        · exact h189
        · exact h190
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_east, advanceAt163_southEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt163_southEast, h163, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h164 : p 164 with
      | false =>
        cases h190 : p 190 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = some (.walk 190) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_east, advanceAt163_southEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt163_southEast, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case176.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case176, memberCase176, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame176.bindings p
          intro binding member
          simp only [frame176, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h163
          · exact h164
          · exact h190
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_east, advanceAt163_southEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt163_southEast, h163, h164, h189, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_east, advanceAt163_southEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt163_southEast, h163, h164, h189, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_east, advanceAt163_southEast, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, cornerAt163_southEast, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover223 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southWest = some outcome) : OracleCovered rowCases223 p outcome := by
  cases h163 : p 163 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_west, advanceAt163_southWest, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, cornerAt163_southWest, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 163 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt163_south, advanceAt163_west, advanceAt163_southWest, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, cornerAt163_southWest, h163, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover224 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .north = some outcome) : OracleCovered rowCases224 p outcome := by
  cases h164 : p 164 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt138_south, advanceAt164_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt164_north, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt138_south, advanceAt164_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt164_north, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover225 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .south = some outcome) : OracleCovered rowCases225 p outcome := by
  cases h164 : p 164 with
  | false =>
    cases h190 : p 190 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .south = some (.walk 190) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt164_south, advanceAt190_north, advanceAt190_south, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt164_south, h164, h190, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case177.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case177, memberCase177, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame177.bindings p
      intro binding member
      simp only [frame177, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h164
      · exact h190
    | true =>
      cases h216 : p 216 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .south = some (.push 190 (.stay 216)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt164_south, advanceAt190_north, advanceAt190_south, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt164_south, h164, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case737.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case737, memberCase737, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame737.bindings p
        intro binding member
        simp only [frame737, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h164
        · exact h190
        · exact h216
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt164_south, advanceAt190_north, advanceAt190_south, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt164_south, h164, h190, h216, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt164_south, advanceAt190_north, advanceAt190_south, advanceAt216_south, advanceAt242_south, advanceAt268_south, advanceAt294_south, advanceAt320_south, advanceAt346_south, advanceAt372_south, advanceAt398_south, advanceAt424_south, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt164_south, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover226 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .east = some outcome) : OracleCovered rowCases226 p outcome := by
  cases h164 : p 164 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt164_east, advanceAt165_east, advanceAt165_west, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt164_east, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt164_east, advanceAt165_east, advanceAt165_west, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt164_east, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover227 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .west = some outcome) : OracleCovered rowCases227 p outcome := by
  cases h164 : p 164 with
  | false =>
    cases h163 : p 163 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .west = some (.walk 163) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_east, advanceAt163_west, advanceAt164_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt164_west, h163, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case178.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case178, memberCase178, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame178.bindings p
      intro binding member
      simp only [frame178, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h163
      · exact h164
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_east, advanceAt163_west, advanceAt164_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt164_west, h163, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 164 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_west, advanceAt161_west, advanceAt162_west, advanceAt163_east, advanceAt163_west, advanceAt164_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, cornerAt164_west, h164, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
