import NetHack.Soko12Forward220.Unified.P03.OracleCover17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover216 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .north = some outcome) : OracleCovered rowCases216 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h134 : p 134 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .north = some (.walk 134) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case158.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case158, memberCase158, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame158.bindings p
      intro binding member
      simp only [frame158, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h134
      · exact h160
    | true =>
      cases h108 : p 108 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .north = some (.push 134 (.stay 108)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h108, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case688.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case688, memberCase688, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame688.bindings p
        intro binding member
        simp only [frame688, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h108
        · exact h134
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h108, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt4_north, advanceAt30_north, advanceAt56_north, advanceAt82_north, advanceAt108_north, advanceAt134_north, advanceAt134_south, advanceAt160_north, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt82, doorAt82, trapAt82, boxAt82, holeAt82, floorAt108, doorAt108, trapAt108, boxAt108, holeAt108, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_north, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover217 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .south = some outcome) : OracleCovered rowCases217 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h186 : p 186 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .south = some (.walk 186) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case159.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case159, memberCase159, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame159.bindings p
      intro binding member
      simp only [frame159, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h160
      · exact h186
    | true =>
      cases h212 : p 212 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .south = some (.push 186 (.stay 212)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, h186, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case733.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case733, memberCase733, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame733.bindings p
        intro binding member
        simp only [frame733, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h160
        · exact h186
        · exact h212
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, h186, h212, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt186_north, advanceAt186_south, advanceAt212_south, advanceAt238_south, advanceAt264_south, advanceAt290_south, advanceAt316_south, advanceAt342_south, advanceAt368_south, advanceAt394_south, advanceAt420_south, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt420, doorAt420, trapAt420, boxAt420, holeAt420, cornerAt160_south, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover218 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .east = some outcome) : OracleCovered rowCases218 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h161 : p 161 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .east = some (.walk 161) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_east, advanceAt161_east, advanceAt161_west, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt160_east, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case160.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case160, memberCase160, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame160.bindings p
      intro binding member
      simp only [frame160, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h160
      · exact h161
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_east, advanceAt161_east, advanceAt161_west, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt160_east, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_east, advanceAt161_east, advanceAt161_west, advanceAt162_east, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt160_east, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover219 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .west = some outcome) : OracleCovered rowCases219 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h159 : p 159 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .west = some (.walk 159) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case161.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case161, memberCase161, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame161.bindings p
      intro binding member
      simp only [frame161, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h159
      · exact h160
    | true =>
      cases h158 : p 158 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .west = some (.push 159 (.stay 158)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h158, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case709.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case709, memberCase709, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame709.bindings p
        intro binding member
        simp only [frame709, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h158
        · exact h159
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h158, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_east, advanceAt159_west, advanceAt160_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_west, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover220 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = some outcome) : OracleCovered rowCases220 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h134 : p 134 with
    | false =>
      cases h135 : p 135 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = some (.walk 135) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_east, advanceAt160_northEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt160_northEast, h134, h135, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case162.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case162, memberCase162, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame162.bindings p
        intro binding member
        simp only [frame162, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h134
        · exact h135
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_east, advanceAt160_northEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt160_northEast, h134, h135, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h161 : p 161 with
      | false =>
        cases h135 : p 135 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = some (.walk 135) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_east, advanceAt160_northEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt160_northEast, h134, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case163.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case163, memberCase163, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame163.bindings p
          intro binding member
          simp only [frame163, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h135
          · exact h160
          · exact h161
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_east, advanceAt160_northEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt160_northEast, h134, h135, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_east, advanceAt160_northEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt160_northEast, h134, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_east, advanceAt160_northEast, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt160_northEast, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover221 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = some outcome) : OracleCovered rowCases221 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h134 : p 134 with
    | false =>
      cases h133 : p 133 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = some (.walk 133) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_west, advanceAt160_northWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_northWest, h133, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case164.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case164, memberCase164, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame164.bindings p
        intro binding member
        simp only [frame164, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h133
        · exact h134
        · exact h160
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_west, advanceAt160_northWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_northWest, h133, h134, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h159 : p 159 with
      | false =>
        cases h133 : p 133 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = some (.walk 133) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_west, advanceAt160_northWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_northWest, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case165.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case165, memberCase165, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame165.bindings p
          intro binding member
          simp only [frame165, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h133
          · exact h159
          · exact h160
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_west, advanceAt160_northWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_northWest, h133, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_west, advanceAt160_northWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_northWest, h134, h159, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_north, advanceAt160_west, advanceAt160_northWest, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, cornerAt160_northWest, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover222 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = some outcome) : OracleCovered rowCases222 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h186 : p 186 with
    | false =>
      cases h187 : p 187 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = some (.walk 187) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_east, advanceAt160_southEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt160_southEast, h160, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case166.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case166, memberCase166, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame166.bindings p
        intro binding member
        simp only [frame166, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h160
        · exact h186
        · exact h187
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_east, advanceAt160_southEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt160_southEast, h160, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h161 : p 161 with
      | false =>
        cases h187 : p 187 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = some (.walk 187) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_east, advanceAt160_southEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt160_southEast, h160, h161, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case167.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case167, memberCase167, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame167.bindings p
          intro binding member
          simp only [frame167, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h160
          · exact h161
          · exact h187
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_east, advanceAt160_southEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt160_southEast, h160, h161, h186, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_east, advanceAt160_southEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt160_southEast, h160, h161, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_east, advanceAt160_southEast, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, cornerAt160_southEast, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover223 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = some outcome) : OracleCovered rowCases223 p outcome := by
  cases h160 : p 160 with
  | false =>
    cases h186 : p 186 with
    | false =>
      cases h185 : p 185 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = some (.walk 185) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_west, advanceAt160_southWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt160_southWest, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case168.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case168, memberCase168, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame168.bindings p
        intro binding member
        simp only [frame168, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h160
        · exact h185
        · exact h186
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_west, advanceAt160_southWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt160_southWest, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h159 : p 159 with
      | false =>
        cases h185 : p 185 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = some (.walk 185) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_west, advanceAt160_southWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt160_southWest, h159, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case169.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case169, memberCase169, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame169.bindings p
          intro binding member
          simp only [frame169, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h159
          · exact h160
          · exact h185
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_west, advanceAt160_southWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt160_southWest, h159, h160, h185, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_west, advanceAt160_southWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt160_southWest, h159, h160, h186, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 160 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt160_south, advanceAt160_west, advanceAt160_southWest, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt185, doorAt185, trapAt185, boxAt185, holeAt185, floorAt186, doorAt186, trapAt186, boxAt186, holeAt186, cornerAt160_southWest, h160, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover224 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .north = some outcome) : OracleCovered rowCases224 p outcome := by
  cases h161 : p 161 with
  | false =>
    cases h135 : p 135 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .north = some (.walk 135) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt135_south, advanceAt161_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_north, h135, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case170.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case170, memberCase170, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame170.bindings p
      intro binding member
      simp only [frame170, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h135
      · exact h161
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt135_south, advanceAt161_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_north, h135, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt135_south, advanceAt161_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_north, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover225 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .south = some outcome) : OracleCovered rowCases225 p outcome := by
  cases h161 : p 161 with
  | false =>
    cases h187 : p 187 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .south = some (.walk 187) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt161_south, advanceAt187_north, advanceAt187_south, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt161_south, h161, h187, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case171.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case171, memberCase171, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame171.bindings p
      intro binding member
      simp only [frame171, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h161
      · exact h187
    | true =>
      cases h213 : p 213 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .south = some (.push 187 (.stay 213)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt161_south, advanceAt187_north, advanceAt187_south, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt161_south, h161, h187, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case737.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case737, memberCase737, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame737.bindings p
        intro binding member
        simp only [frame737, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h161
        · exact h187
        · exact h213
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt161_south, advanceAt187_north, advanceAt187_south, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt161_south, h161, h187, h213, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt161_south, advanceAt187_north, advanceAt187_south, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt161_south, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover226 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .east = some outcome) : OracleCovered rowCases226 p outcome := by
  cases h161 : p 161 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt161_east, advanceAt162_east, advanceAt162_west, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt161_east, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt161_east, advanceAt162_east, advanceAt162_west, advanceAt163_east, advanceAt164_east, advanceAt165_east, advanceAt166_east, advanceAt167_east, advanceAt168_east, advanceAt169_east, advanceAt170_east, advanceAt171_east, advanceAt172_east, advanceAt173_east, advanceAt174_east, advanceAt175_east, advanceAt176_east, advanceAt177_east, advanceAt178_east, advanceAt179_east, advanceAt180_east, advanceAt181_east, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt168, doorAt168, trapAt168, boxAt168, holeAt168, floorAt169, doorAt169, trapAt169, boxAt169, holeAt169, floorAt170, doorAt170, trapAt170, boxAt170, holeAt170, floorAt171, doorAt171, trapAt171, boxAt171, holeAt171, floorAt172, doorAt172, trapAt172, boxAt172, holeAt172, floorAt173, doorAt173, trapAt173, boxAt173, holeAt173, floorAt174, doorAt174, trapAt174, boxAt174, holeAt174, floorAt175, doorAt175, trapAt175, boxAt175, holeAt175, floorAt176, doorAt176, trapAt176, boxAt176, holeAt176, floorAt177, doorAt177, trapAt177, boxAt177, holeAt177, floorAt178, doorAt178, trapAt178, boxAt178, holeAt178, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt180, doorAt180, trapAt180, boxAt180, holeAt180, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, cornerAt161_east, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover227 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .west = some outcome) : OracleCovered rowCases227 p outcome := by
  cases h161 : p 161 with
  | false =>
    cases h160 : p 160 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .west = some (.walk 160) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_east, advanceAt160_west, advanceAt161_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_west, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case172.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case172, memberCase172, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame172.bindings p
      intro binding member
      simp only [frame172, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h160
      · exact h161
    | true =>
      cases h159 : p 159 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .west = some (.push 160 (.stay 159)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_east, advanceAt160_west, advanceAt161_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_west, h159, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case713.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case713, memberCase713, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame713.bindings p
        intro binding member
        simp only [frame713, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h159
        · exact h160
        · exact h161
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_east, advanceAt160_west, advanceAt161_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_west, h159, h160, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 161 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt156_west, advanceAt157_west, advanceAt158_west, advanceAt159_west, advanceAt160_east, advanceAt160_west, advanceAt161_west, floorAt156, doorAt156, trapAt156, boxAt156, holeAt156, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt158, doorAt158, trapAt158, boxAt158, holeAt158, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, cornerAt161_west, h161, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P03
