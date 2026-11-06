import NetHack.Soko12Forward220.Unified.P01.OracleCover15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover192 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .north = some outcome) : OracleCovered rowCases192 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h133 : p 133 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .north = some (.walk 133) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt133_south, advanceAt159_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_north, h133, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case142.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case142, memberCase142, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame142.bindings p
      intro binding member
      simp only [frame142, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h133
      · exact h159
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt133_south, advanceAt159_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_north, h133, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt29_north, advanceAt55_north, advanceAt81_north, advanceAt107_north, advanceAt133_north, advanceAt133_south, advanceAt159_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt81, doorAt81, trapAt81, boxAt81, holeAt81, floorAt107, doorAt107, trapAt107, boxAt107, holeAt107, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_north, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover193 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .south = some outcome) : OracleCovered rowCases193 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h185 : p 185 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .south = some (.walk 185) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt185_north, advanceAt185_south, advanceAt211_south, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt159_south, h159, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case143.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case143, memberCase143, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame143.bindings p
      intro binding member
      simp only [frame143, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h159
      · exact h185
    | true =>
      cases h211 : p 211 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .south = some (.push 185 (.stay 211)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt185_north, advanceAt185_south, advanceAt211_south, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt159_south, h159, h185, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case725.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case725, memberCase725, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame725.bindings p
        intro binding member
        simp only [frame725, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h185
        · exact h211
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt185_north, advanceAt185_south, advanceAt211_south, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt159_south, h159, h185, h211, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt185_north, advanceAt185_south, advanceAt211_south, advanceAt237_south, advanceAt263_south, advanceAt289_south, advanceAt315_south, advanceAt341_south, advanceAt367_south, advanceAt393_south, advanceAt419_south, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt237, doorAt237, trapAt237, boxAt237, holeAt237, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt289, doorAt289, trapAt289, boxAt289, holeAt289, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt419, doorAt419, trapAt419, boxAt419, holeAt419, cornerAt159_south, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover194 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .east = some outcome) : OracleCovered rowCases194 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h160 : p 160 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .east = some (.walk 160) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_east, advanceAt160_east, advanceAt160_west, advanceAt161_east, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt159_east, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case144.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case144, memberCase144, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame144.bindings p
      intro binding member
      simp only [frame144, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h159
      · exact h160
    | true =>
      cases h161 : p 161 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .east = some (.push 160 (.stay 161)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_east, advanceAt160_east, advanceAt160_west, advanceAt161_east, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt159_east, h159, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case708.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case708, memberCase708, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame708.bindings p
        intro binding member
        simp only [frame708, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h160
        · exact h161
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_east, advanceAt160_east, advanceAt160_west, advanceAt161_east, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt159_east, h159, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_east, advanceAt160_east, advanceAt160_west, advanceAt161_east, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt159_east, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover195 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .west = some outcome) : OracleCovered rowCases195 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h158 : p 158 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .west = some (.walk 158) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_east, advanceAt158_west, advanceAt159_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_west, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case145.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case145, memberCase145, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame145.bindings p
      intro binding member
      simp only [frame145, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h158
      · exact h159
    | true =>
      cases h157 : p 157 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .west = some (.push 158 (.stay 157)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_east, advanceAt158_west, advanceAt159_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_west, h157, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case701.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case701, memberCase701, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame701.bindings p
        intro binding member
        simp only [frame701, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h157
        · exact h158
        · exact h159
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_east, advanceAt158_west, advanceAt159_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_west, h157, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_east, advanceAt158_west, advanceAt159_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_west, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover196 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = some outcome) : OracleCovered rowCases196 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h133 : p 133 with
    | false =>
      cases h134 : p 134 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = some (.walk 134) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_east, advanceAt159_northEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt159_northEast, h133, h134, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case146.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case146, memberCase146, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame146.bindings p
        intro binding member
        simp only [frame146, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h133
        · exact h134
        · exact h159
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_east, advanceAt159_northEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt159_northEast, h133, h134, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h160 : p 160 with
      | false =>
        cases h134 : p 134 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = some (.walk 134) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_east, advanceAt159_northEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt159_northEast, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case147.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case147, memberCase147, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame147.bindings p
          intro binding member
          simp only [frame147, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h134
          · exact h159
          · exact h160
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_east, advanceAt159_northEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt159_northEast, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_east, advanceAt159_northEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt159_northEast, h133, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_east, advanceAt159_northEast, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt159_northEast, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover197 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = some outcome) : OracleCovered rowCases197 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h133 : p 133 with
    | false =>
      cases h132 : p 132 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = some (.walk 132) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_west, advanceAt159_northWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_northWest, h132, h133, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case148.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case148, memberCase148, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame148.bindings p
        intro binding member
        simp only [frame148, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h132
        · exact h133
        · exact h159
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_west, advanceAt159_northWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_northWest, h132, h133, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h158 : p 158 with
      | false =>
        cases h132 : p 132 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = some (.walk 132) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_west, advanceAt159_northWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_northWest, h132, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case149.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case149, memberCase149, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame149.bindings p
          intro binding member
          simp only [frame149, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h132
          · exact h158
          · exact h159
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_west, advanceAt159_northWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_northWest, h132, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_west, advanceAt159_northWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_northWest, h133, h158, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_north, advanceAt159_west, advanceAt159_northWest, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, cornerAt159_northWest, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover198 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = some outcome) : OracleCovered rowCases198 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h185 : p 185 with
    | false =>
      cases h186 : p 186 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = some (.walk 186) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_east, advanceAt159_southEast, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt159_southEast, h159, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case150.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case150, memberCase150, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame150.bindings p
        intro binding member
        simp only [frame150, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h185
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_east, advanceAt159_southEast, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt159_southEast, h159, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h160 : p 160 with
      | false =>
        cases h186 : p 186 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = some (.walk 186) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_east, advanceAt159_southEast, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt159_southEast, h159, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case151.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case151, memberCase151, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame151.bindings p
          intro binding member
          simp only [frame151, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h159
          · exact h160
          · exact h186
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_east, advanceAt159_southEast, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt159_southEast, h159, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_east, advanceAt159_southEast, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt159_southEast, h159, h160, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_east, advanceAt159_southEast, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt159_southEast, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover199 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = some outcome) : OracleCovered rowCases199 p outcome := by
  cases h159 : p 159 with
  | false =>
    cases h185 : p 185 with
    | false =>
      cases h184 : p 184 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = some (.walk 184) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_west, advanceAt159_southWest, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, cornerAt159_southWest, h159, h184, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case152.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case152, memberCase152, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame152.bindings p
        intro binding member
        simp only [frame152, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h184
        · exact h185
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_west, advanceAt159_southWest, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, cornerAt159_southWest, h159, h184, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h158 : p 158 with
      | false =>
        cases h184 : p 184 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = some (.walk 184) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_west, advanceAt159_southWest, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, cornerAt159_southWest, h158, h159, h184, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case153.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case153, memberCase153, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame153.bindings p
          intro binding member
          simp only [frame153, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h158
          · exact h159
          · exact h184
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_west, advanceAt159_southWest, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, cornerAt159_southWest, h158, h159, h184, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_west, advanceAt159_southWest, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, cornerAt159_southWest, h158, h159, h185, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 159 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt159_south, advanceAt159_west, advanceAt159_southWest, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, cornerAt159_southWest, h159, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover200 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .north = some outcome) : OracleCovered rowCases200 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h134 : p 134 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .north = some (.walk 134) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case154.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case154, memberCase154, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame154.bindings p
      intro binding member
      simp only [frame154, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h134
      · exact h160
    | true =>
      cases h108 : p 108 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .north = some (.push 134 (.stay 108)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h108, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case684.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case684, memberCase684, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame684.bindings p
        intro binding member
        simp only [frame684, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h108
        · exact h134
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h108, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover201 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .south = some outcome) : OracleCovered rowCases201 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h186 : p 186 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .south = some (.walk 186) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case155.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case155, memberCase155, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame155.bindings p
      intro binding member
      simp only [frame155, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h160
      · exact h186
    | true =>
      cases h212 : p 212 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .south = some (.push 186 (.stay 212)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, h186, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case729.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case729, memberCase729, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame729.bindings p
        intro binding member
        simp only [frame729, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h160
        · exact h186
        · exact h212
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, h186, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover202 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .east = some outcome) : OracleCovered rowCases202 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h161 : p 161 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .east = some (.walk 161) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_east, advanceAt161_east, advanceAt161_west, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt160_east, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case156.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case156, memberCase156, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame156.bindings p
      intro binding member
      simp only [frame156, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h160
      · exact h161
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_east, advanceAt161_east, advanceAt161_west, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt160_east, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_east, advanceAt161_east, advanceAt161_west, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt160_east, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover203 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .west = some outcome) : OracleCovered rowCases203 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h159 : p 159 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .west = some (.walk 159) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case157.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case157, memberCase157, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame157.bindings p
      intro binding member
      simp only [frame157, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h159
      · exact h160
    | true =>
      cases h158 : p 158 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .west = some (.push 159 (.stay 158)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h158, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case705.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case705, memberCase705, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame705.bindings p
        intro binding member
        simp only [frame705, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h158
        · exact h159
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h158, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 160 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
