import NetHack.Soko12Forward220.Unified.P01.OracleCover57
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P01
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover696 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .north = some outcome) : OracleCovered rowCases696 p outcome := by
  cases h372 : p 372 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt242_north, advanceAt268_north, advanceAt294_north, advanceAt320_north, advanceAt346_north, advanceAt346_south, advanceAt372_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_north, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt34_north, advanceAt60_north, advanceAt86_north, advanceAt112_north, advanceAt138_north, advanceAt164_north, advanceAt190_north, advanceAt216_north, advanceAt242_north, advanceAt268_north, advanceAt294_north, advanceAt320_north, advanceAt346_north, advanceAt346_south, advanceAt372_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt60, doorAt60, trapAt60, boxAt60, holeAt60, floorAt86, doorAt86, trapAt86, boxAt86, holeAt86, floorAt112, doorAt112, trapAt112, boxAt112, holeAt112, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt164, doorAt164, trapAt164, boxAt164, holeAt164, floorAt190, doorAt190, trapAt190, boxAt190, holeAt190, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt242, doorAt242, trapAt242, boxAt242, holeAt242, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt294, doorAt294, trapAt294, boxAt294, holeAt294, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_north, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover697 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .south = some outcome) : OracleCovered rowCases697 p outcome := by
  cases h372 : p 372 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt398_north, advanceAt398_south, advanceAt424_south, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt372_south, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt398_north, advanceAt398_south, advanceAt424_south, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, cornerAt372_south, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover698 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .east = some outcome) : OracleCovered rowCases698 p outcome := by
  cases h372 : p 372 with
  | false =>
    cases h373 : p 373 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .east = some (.walk 373) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_east, advanceAt373_east, advanceAt373_west, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt372_east, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case635.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case635, memberCase635, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame635.bindings p
      intro binding member
      simp only [frame635, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h372
      · exact h373
    | true =>
      cases h374 : p 374 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .east = some (.push 373 (.stay 374)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_east, advanceAt373_east, advanceAt373_west, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt372_east, h372, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case852.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case852, memberCase852, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame852.bindings p
        intro binding member
        simp only [frame852, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h372
        · exact h373
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_east, advanceAt373_east, advanceAt373_west, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt372_east, h372, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_east, advanceAt373_east, advanceAt373_west, advanceAt374_east, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt372_east, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover699 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .west = some outcome) : OracleCovered rowCases699 p outcome := by
  cases h372 : p 372 with
  | false =>
    cases h371 : p 371 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .west = some (.walk 371) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_east, advanceAt371_west, advanceAt372_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_west, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case636.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case636, memberCase636, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame636.bindings p
      intro binding member
      simp only [frame636, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h371
      · exact h372
    | true =>
      cases h370 : p 370 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .west = some (.push 371 (.stay 370)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_east, advanceAt371_west, advanceAt372_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_west, h370, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case849.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case849, memberCase849, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame849.bindings p
        intro binding member
        simp only [frame849, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h370
        · exact h371
        · exact h372
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_east, advanceAt371_west, advanceAt372_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_west, h370, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_east, advanceAt371_west, advanceAt372_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_west, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover700 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northEast = some outcome) : OracleCovered rowCases700 p outcome := by
  cases h372 : p 372 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_north, advanceAt372_east, advanceAt372_northEast, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt372_northEast, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_north, advanceAt372_east, advanceAt372_northEast, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt372_northEast, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover701 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northWest = some outcome) : OracleCovered rowCases701 p outcome := by
  cases h372 : p 372 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h345 : p 345 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northWest = some (.walk 345) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_north, advanceAt372_west, advanceAt372_northWest, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_northWest, h345, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case637.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case637, memberCase637, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame637.bindings p
        intro binding member
        simp only [frame637, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h371
        · exact h372
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_north, advanceAt372_west, advanceAt372_northWest, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_northWest, h345, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_north, advanceAt372_west, advanceAt372_northWest, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_northWest, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_north, advanceAt372_west, advanceAt372_northWest, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt372_northWest, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover702 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southEast = some outcome) : OracleCovered rowCases702 p outcome := by
  cases h372 : p 372 with
  | false =>
    cases h373 : p 373 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southEast = some (.walk 399) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_east, advanceAt372_southEast, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, cornerAt372_southEast, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case638.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case638, memberCase638, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame638.bindings p
      intro binding member
      simp only [frame638, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h372
      · exact h373
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_east, advanceAt372_southEast, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, cornerAt372_southEast, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_east, advanceAt372_southEast, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, cornerAt372_southEast, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover703 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southWest = some outcome) : OracleCovered rowCases703 p outcome := by
  cases h372 : p 372 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h397 : p 397 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southWest = some (.walk 397) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_west, advanceAt372_southWest, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, cornerAt372_southWest, h371, h372, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case639.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case639, memberCase639, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame639.bindings p
        intro binding member
        simp only [frame639, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h371
        · exact h372
        · exact h397
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_west, advanceAt372_southWest, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, cornerAt372_southWest, h371, h372, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_west, advanceAt372_southWest, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, cornerAt372_southWest, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 372 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt372_south, advanceAt372_west, advanceAt372_southWest, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, cornerAt372_southWest, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover704 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .north = some outcome) : OracleCovered rowCases704 p outcome := by
  cases h373 : p 373 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt35_north, advanceAt61_north, advanceAt87_north, advanceAt113_north, advanceAt139_north, advanceAt165_north, advanceAt191_north, advanceAt217_north, advanceAt243_north, advanceAt269_north, advanceAt295_north, advanceAt321_north, advanceAt347_north, advanceAt347_south, advanceAt373_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt373_north, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt9_north, advanceAt35_north, advanceAt61_north, advanceAt87_north, advanceAt113_north, advanceAt139_north, advanceAt165_north, advanceAt191_north, advanceAt217_north, advanceAt243_north, advanceAt269_north, advanceAt295_north, advanceAt321_north, advanceAt347_north, advanceAt347_south, advanceAt373_north, floorAt9, doorAt9, trapAt9, boxAt9, holeAt9, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt61, doorAt61, trapAt61, boxAt61, holeAt61, floorAt87, doorAt87, trapAt87, boxAt87, holeAt87, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt295, doorAt295, trapAt295, boxAt295, holeAt295, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt373_north, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover705 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .south = some outcome) : OracleCovered rowCases705 p outcome := by
  cases h373 : p 373 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .south = some (.walk 399) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt373_south, advanceAt399_north, advanceAt399_south, advanceAt425_south, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, cornerAt373_south, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case640.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case640, memberCase640, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame640.bindings p
    intro binding member
    simp only [frame640, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h373
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt373_south, advanceAt399_north, advanceAt399_south, advanceAt425_south, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, cornerAt373_south, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover706 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .east = some outcome) : OracleCovered rowCases706 p outcome := by
  cases h373 : p 373 with
  | false =>
    cases h374 : p 374 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .east = some (.walk 374) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt373_east, advanceAt374_east, advanceAt374_west, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt373_east, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case641.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case641, memberCase641, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame641.bindings p
      intro binding member
      simp only [frame641, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h373
      · exact h374
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt373_east, advanceAt374_east, advanceAt374_west, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt373_east, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt373_east, advanceAt374_east, advanceAt374_west, advanceAt375_east, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt373_east, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover707 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .west = some outcome) : OracleCovered rowCases707 p outcome := by
  cases h373 : p 373 with
  | false =>
    cases h372 : p 372 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .west = some (.walk 372) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_east, advanceAt372_west, advanceAt373_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt373_west, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case642.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case642, memberCase642, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame642.bindings p
      intro binding member
      simp only [frame642, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h372
      · exact h373
    | true =>
      cases h371 : p 371 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .west = some (.push 372 (.stay 371)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_east, advanceAt372_west, advanceAt373_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt373_west, h371, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case851.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case851, memberCase851, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame851.bindings p
        intro binding member
        simp only [frame851, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h371
        · exact h372
        · exact h373
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_east, advanceAt372_west, advanceAt373_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt373_west, h371, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 1) p) (project (soko1_2.initial.holes.drop 1)) 373 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_east, advanceAt372_west, advanceAt373_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, cornerAt373_west, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P01
