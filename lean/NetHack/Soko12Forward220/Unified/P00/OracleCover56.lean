import NetHack.Soko12Forward220.Unified.P00.OracleCover55
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover672 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .north = some outcome) : OracleCovered rowCases672 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt344_south, advanceAt370_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, cornerAt370_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt344_south, advanceAt370_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, cornerAt370_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover673 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .south = some outcome) : OracleCovered rowCases673 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .south = some (.walk 396) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt396_north, advanceAt396_south, advanceAt422_south, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt370_south, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case623.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case623, memberCase623, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame623.bindings p
    intro binding member
    simp only [frame623, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h370
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt396_north, advanceAt396_south, advanceAt422_south, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt370_south, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover674 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .east = some outcome) : OracleCovered rowCases674 p outcome := by
  cases h370 : p 370 with
  | false =>
    cases h371 : p 371 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .east = some (.walk 371) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_east, advanceAt371_east, advanceAt371_west, advanceAt372_east, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt370_east, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case624.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case624, memberCase624, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame624.bindings p
      intro binding member
      simp only [frame624, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h370
      · exact h371
    | true =>
      cases h372 : p 372 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .east = some (.push 371 (.stay 372)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_east, advanceAt371_east, advanceAt371_west, advanceAt372_east, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt370_east, h370, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case846.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case846, memberCase846, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame846.bindings p
        intro binding member
        simp only [frame846, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h370
        · exact h371
        · exact h372
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_east, advanceAt371_east, advanceAt371_west, advanceAt372_east, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt370_east, h370, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_east, advanceAt371_east, advanceAt371_west, advanceAt372_east, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt370_east, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover675 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .west = some outcome) : OracleCovered rowCases675 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_east, advanceAt369_west, advanceAt370_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, cornerAt370_west, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_east, advanceAt369_west, advanceAt370_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, cornerAt370_west, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover676 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northEast = some outcome) : OracleCovered rowCases676 p outcome := by
  cases h370 : p 370 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northEast = some (.walk 345) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_north, advanceAt370_east, advanceAt370_northEast, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt370_northEast, h345, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case625.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case625, memberCase625, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame625.bindings p
        intro binding member
        simp only [frame625, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h370
        · exact h371
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_north, advanceAt370_east, advanceAt370_northEast, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt370_northEast, h345, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_north, advanceAt370_east, advanceAt370_northEast, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt370_northEast, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_north, advanceAt370_east, advanceAt370_northEast, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt370_northEast, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover677 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northWest = some outcome) : OracleCovered rowCases677 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_north, advanceAt370_west, advanceAt370_northWest, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, cornerAt370_northWest, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_north, advanceAt370_west, advanceAt370_northWest, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, cornerAt370_northWest, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover678 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southEast = some outcome) : OracleCovered rowCases678 p outcome := by
  cases h370 : p 370 with
  | false =>
    cases h397 : p 397 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southEast = some (.walk 397) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt370_east, advanceAt370_southEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt370_southEast, h370, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case626.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case626, memberCase626, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame626.bindings p
      intro binding member
      simp only [frame626, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h370
      · exact h397
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt370_east, advanceAt370_southEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt370_southEast, h370, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt370_east, advanceAt370_southEast, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, cornerAt370_southEast, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover679 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southWest = some outcome) : OracleCovered rowCases679 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt370_west, advanceAt370_southWest, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt370_southWest, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 370 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt370_south, advanceAt370_west, advanceAt370_southWest, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt370_southWest, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover680 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .north = some outcome) : OracleCovered rowCases680 p outcome := by
  cases h371 : p 371 with
  | false =>
    cases h345 : p 345 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .north = some (.walk 345) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt345_south, advanceAt371_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_north, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case627.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case627, memberCase627, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame627.bindings p
      intro binding member
      simp only [frame627, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h345
      · exact h371
    | true =>
      cases h319 : p 319 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .north = some (.push 345 (.stay 319)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt345_south, advanceAt371_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_north, h319, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case840.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case840, memberCase840, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame840.bindings p
        intro binding member
        simp only [frame840, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h319
        · exact h345
        · exact h371
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt345_south, advanceAt371_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_north, h319, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt33_north, advanceAt59_north, advanceAt85_north, advanceAt111_north, advanceAt137_north, advanceAt163_north, advanceAt189_north, advanceAt215_north, advanceAt241_north, advanceAt267_north, advanceAt293_north, advanceAt319_north, advanceAt345_north, advanceAt345_south, advanceAt371_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt59, doorAt59, trapAt59, boxAt59, holeAt59, floorAt85, doorAt85, trapAt85, boxAt85, holeAt85, floorAt111, doorAt111, trapAt111, boxAt111, holeAt111, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt163, doorAt163, trapAt163, boxAt163, holeAt163, floorAt189, doorAt189, trapAt189, boxAt189, holeAt189, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt241, doorAt241, trapAt241, boxAt241, holeAt241, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt293, doorAt293, trapAt293, boxAt293, holeAt293, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_north, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover681 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .south = some outcome) : OracleCovered rowCases681 p outcome := by
  cases h371 : p 371 with
  | false =>
    cases h397 : p 397 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .south = some (.walk 397) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_south, advanceAt397_north, advanceAt397_south, advanceAt423_south, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt371_south, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case628.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case628, memberCase628, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame628.bindings p
      intro binding member
      simp only [frame628, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h371
      · exact h397
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_south, advanceAt397_north, advanceAt397_south, advanceAt423_south, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt371_south, h371, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_south, advanceAt397_north, advanceAt397_south, advanceAt423_south, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt423, doorAt423, trapAt423, boxAt423, holeAt423, cornerAt371_south, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover682 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .east = some outcome) : OracleCovered rowCases682 p outcome := by
  cases h371 : p 371 with
  | false =>
    cases h372 : p 372 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .east = some (.walk 372) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_east, advanceAt372_east, advanceAt372_west, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt371_east, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case629.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case629, memberCase629, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame629.bindings p
      intro binding member
      simp only [frame629, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h371
      · exact h372
    | true =>
      cases h373 : p 373 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .east = some (.push 372 (.stay 373)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_east, advanceAt372_east, advanceAt372_west, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt371_east, h371, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case848.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case848, memberCase848, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame848.bindings p
        intro binding member
        simp only [frame848, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h371
        · exact h372
        · exact h373
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_east, advanceAt372_east, advanceAt372_west, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt371_east, h371, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt371_east, advanceAt372_east, advanceAt372_west, advanceAt373_east, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt371_east, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover683 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .west = some outcome) : OracleCovered rowCases683 p outcome := by
  cases h371 : p 371 with
  | false =>
    cases h370 : p 370 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .west = some (.walk 370) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_east, advanceAt370_west, advanceAt371_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_west, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case630.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case630, memberCase630, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame630.bindings p
      intro binding member
      simp only [frame630, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h370
      · exact h371
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_east, advanceAt370_west, advanceAt371_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_west, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 371 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_east, advanceAt370_west, advanceAt371_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt371_west, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
