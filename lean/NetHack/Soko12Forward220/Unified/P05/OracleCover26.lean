import NetHack.Soko12Forward220.Unified.P05.OracleCover25
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover312 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .north = some outcome) : OracleCovered rowCases312 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h160 : p 160 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .north = some (.walk 160) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt160_south, advanceAt186_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_north, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case245.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case245, memberCase245, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame245.bindings p
      intro binding member
      simp only [frame245, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h160
      · exact h186
    | true =>
      cases h134 : p 134 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .north = some (.push 160 (.stay 134)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt160_south, advanceAt186_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_north, h134, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case714.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case714, memberCase714, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame714.bindings p
        intro binding member
        simp only [frame714, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h134
        · exact h160
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt160_south, advanceAt186_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_north, h134, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt160_north, advanceAt160_south, advanceAt186_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_north, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover313 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .south = some outcome) : OracleCovered rowCases313 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h212 : p 212 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .south = some (.walk 212) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt212_north, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt186_south, h186, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case246.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case246, memberCase246, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame246.bindings p
      intro binding member
      simp only [frame246, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h186
      · exact h212
    | true =>
      cases h238 : p 238 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .south = some (.push 212 (.stay 238)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt212_north, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt186_south, h186, h212, h238, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case767.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case767, memberCase767, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame767.bindings p
        intro binding member
        simp only [frame767, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h186
        · exact h212
        · exact h238
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt212_north, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt186_south, h186, h212, h238, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt212_north, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt186_south, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover314 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .east = some outcome) : OracleCovered rowCases314 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h187 : p 187 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .east = some (.walk 187) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_east, advanceAt187_east, advanceAt187_west, advanceAt188_east, advanceAt189_east, advanceAt190_east, advanceAt191_east, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt186_east, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case247.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case247, memberCase247, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame247.bindings p
      intro binding member
      simp only [frame247, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h186
      · exact h187
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_east, advanceAt187_east, advanceAt187_west, advanceAt188_east, advanceAt189_east, advanceAt190_east, advanceAt191_east, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt186_east, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_east, advanceAt187_east, advanceAt187_west, advanceAt188_east, advanceAt189_east, advanceAt190_east, advanceAt191_east, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt186_east, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover315 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .west = some outcome) : OracleCovered rowCases315 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h185 : p 185 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .west = some (.walk 185) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_east, advanceAt185_west, advanceAt186_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_west, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case248.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case248, memberCase248, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame248.bindings p
      intro binding member
      simp only [frame248, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h185
      · exact h186
    | true =>
      cases h184 : p 184 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .west = some (.push 185 (.stay 184)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_east, advanceAt185_west, advanceAt186_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_west, h184, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case735.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case735, memberCase735, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame735.bindings p
        intro binding member
        simp only [frame735, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h184
        · exact h185
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_east, advanceAt185_west, advanceAt186_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_west, h184, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_east, advanceAt185_west, advanceAt186_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_west, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover316 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = some outcome) : OracleCovered rowCases316 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h160 : p 160 with
    | false =>
      cases h161 : p 161 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = some (.walk 161) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_east, advanceAt186_northEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt186_northEast, h160, h161, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case249.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case249, memberCase249, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame249.bindings p
        intro binding member
        simp only [frame249, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h160
        · exact h161
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_east, advanceAt186_northEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt186_northEast, h160, h161, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h187 : p 187 with
      | false =>
        cases h161 : p 161 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = some (.walk 161) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_east, advanceAt186_northEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt186_northEast, h160, h161, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case250.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case250, memberCase250, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame250.bindings p
          intro binding member
          simp only [frame250, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h161
          · exact h186
          · exact h187
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_east, advanceAt186_northEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt186_northEast, h160, h161, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_east, advanceAt186_northEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt186_northEast, h160, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_east, advanceAt186_northEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt186_northEast, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover317 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = some outcome) : OracleCovered rowCases317 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h160 : p 160 with
    | false =>
      cases h159 : p 159 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = some (.walk 159) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_west, advanceAt186_northWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_northWest, h159, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case251.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case251, memberCase251, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame251.bindings p
        intro binding member
        simp only [frame251, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h160
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_west, advanceAt186_northWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_northWest, h159, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h185 : p 185 with
      | false =>
        cases h159 : p 159 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = some (.walk 159) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_west, advanceAt186_northWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_northWest, h159, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case252.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case252, memberCase252, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame252.bindings p
          intro binding member
          simp only [frame252, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h159
          · exact h185
          · exact h186
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_west, advanceAt186_northWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_northWest, h159, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_west, advanceAt186_northWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_northWest, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_north, advanceAt186_west, advanceAt186_northWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt186_northWest, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover318 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = some outcome) : OracleCovered rowCases318 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h212 : p 212 with
    | false =>
      cases h213 : p 213 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = some (.walk 213) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_east, advanceAt186_southEast, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt186_southEast, h186, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case253.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case253, memberCase253, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame253.bindings p
        intro binding member
        simp only [frame253, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h186
        · exact h212
        · exact h213
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_east, advanceAt186_southEast, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt186_southEast, h186, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h187 : p 187 with
      | false =>
        cases h213 : p 213 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = some (.walk 213) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_east, advanceAt186_southEast, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt186_southEast, h186, h187, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case254.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case254, memberCase254, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame254.bindings p
          intro binding member
          simp only [frame254, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h186
          · exact h187
          · exact h213
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_east, advanceAt186_southEast, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt186_southEast, h186, h187, h212, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_east, advanceAt186_southEast, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt186_southEast, h186, h187, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_east, advanceAt186_southEast, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, cornerAt186_southEast, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover319 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = some outcome) : OracleCovered rowCases319 p outcome := by
  cases h186 : p 186 with
  | false =>
    cases h212 : p 212 with
    | false =>
      cases h211 : p 211 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = some (.walk 211) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_west, advanceAt186_southWest, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, cornerAt186_southWest, h186, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case255.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case255, memberCase255, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame255.bindings p
        intro binding member
        simp only [frame255, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h186
        · exact h211
        · exact h212
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_west, advanceAt186_southWest, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, cornerAt186_southWest, h186, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h185 : p 185 with
      | false =>
        cases h211 : p 211 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = some (.walk 211) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_west, advanceAt186_southWest, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, cornerAt186_southWest, h185, h186, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case256.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case256, memberCase256, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame256.bindings p
          intro binding member
          simp only [frame256, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h185
          · exact h186
          · exact h211
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_west, advanceAt186_southWest, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, cornerAt186_southWest, h185, h186, h211, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_west, advanceAt186_southWest, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, cornerAt186_southWest, h185, h186, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 186 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt186_south, advanceAt186_west, advanceAt186_southWest, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, cornerAt186_southWest, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover320 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .north = some outcome) : OracleCovered rowCases320 p outcome := by
  cases h187 : p 187 with
  | false =>
    cases h161 : p 161 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .north = some (.walk 161) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt161_south, advanceAt187_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_north, h161, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case257.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case257, memberCase257, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame257.bindings p
      intro binding member
      simp only [frame257, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h161
      · exact h187
    | true =>
      cases h135 : p 135 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .north = some (.push 161 (.stay 135)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt161_south, advanceAt187_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_north, h135, h161, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case718.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case718, memberCase718, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame718.bindings p
        intro binding member
        simp only [frame718, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h135
        · exact h161
        · exact h187
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt161_south, advanceAt187_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_north, h135, h161, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt161_south, advanceAt187_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_north, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover321 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .south = some outcome) : OracleCovered rowCases321 p outcome := by
  cases h187 : p 187 with
  | false =>
    cases h213 : p 213 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .south = some (.walk 213) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt187_south, advanceAt213_north, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt187_south, h187, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case258.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case258, memberCase258, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame258.bindings p
      intro binding member
      simp only [frame258, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h187
      · exact h213
    | true =>
      cases h239 : p 239 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .south = some (.push 213 (.stay 239)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt187_south, advanceAt213_north, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt187_south, h187, h213, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case771.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case771, memberCase771, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame771.bindings p
        intro binding member
        simp only [frame771, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h187
        · exact h213
        · exact h239
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt187_south, advanceAt213_north, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt187_south, h187, h213, h239, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt187_south, advanceAt213_north, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt187_south, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover322 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .east = some outcome) : OracleCovered rowCases322 p outcome := by
  cases h187 : p 187 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt187_east, advanceAt188_east, advanceAt188_west, advanceAt189_east, advanceAt190_east, advanceAt191_east, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt187_east, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt187_east, advanceAt188_east, advanceAt188_west, advanceAt189_east, advanceAt190_east, advanceAt191_east, advanceAt192_east, advanceAt193_east, advanceAt194_east, advanceAt195_east, advanceAt196_east, advanceAt197_east, advanceAt198_east, advanceAt199_east, advanceAt200_east, advanceAt201_east, advanceAt202_east, advanceAt203_east, advanceAt204_east, advanceAt205_east, advanceAt206_east, advanceAt207_east, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt194, doorAt194, trapAt194, boxAt194, holeAt194, floorAt195, doorAt195, trapAt195, boxAt195, holeAt195, floorAt196, doorAt196, trapAt196, boxAt196, holeAt196, floorAt197, doorAt197, trapAt197, boxAt197, holeAt197, floorAt198, doorAt198, trapAt198, boxAt198, holeAt198, floorAt199, doorAt199, trapAt199, boxAt199, holeAt199, floorAt200, doorAt200, trapAt200, boxAt200, holeAt200, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt202, doorAt202, trapAt202, boxAt202, holeAt202, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt207, doorAt207, trapAt207, boxAt207, holeAt207, cornerAt187_east, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover323 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .west = some outcome) : OracleCovered rowCases323 p outcome := by
  cases h187 : p 187 with
  | false =>
    cases h186 : p 186 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .west = some (.walk 186) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_east, advanceAt186_west, advanceAt187_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_west, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case259.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case259, memberCase259, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame259.bindings p
      intro binding member
      simp only [frame259, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h186
      · exact h187
    | true =>
      cases h185 : p 185 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .west = some (.push 186 (.stay 185)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_east, advanceAt186_west, advanceAt187_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_west, h185, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case739.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case739, memberCase739, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame739.bindings p
        intro binding member
        simp only [frame739, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h185
        · exact h186
        · exact h187
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_east, advanceAt186_west, advanceAt187_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_west, h185, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 187 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt182_west, advanceAt183_west, advanceAt184_west, advanceAt185_west, advanceAt186_east, advanceAt186_west, advanceAt187_west, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt187_west, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P05
