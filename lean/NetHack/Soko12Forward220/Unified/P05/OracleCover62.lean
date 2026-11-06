import NetHack.Soko12Forward220.Unified.P05.OracleCover61
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P05
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover744 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .north = some outcome) : OracleCovered rowCases744 p outcome := by
  cases h374 : p 374 with
  | false =>
    cases h348 : p 348 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .north = some (.walk 348) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt348_south, advanceAt374_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_north, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case653.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case653, memberCase653, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame653.bindings p
      intro binding member
      simp only [frame653, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h348
      · exact h374
    | true =>
      cases h322 : p 322 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .north = some (.push 348 (.stay 322)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt348_south, advanceAt374_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_north, h322, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case852.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case852, memberCase852, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame852.bindings p
        intro binding member
        simp only [frame852, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h322
        · exact h348
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt348_south, advanceAt374_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_north, h322, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt348_south, advanceAt374_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_north, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover745 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .south = some outcome) : OracleCovered rowCases745 p outcome := by
  cases h374 : p 374 with
  | false =>
    cases h400 : p 400 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .south = some (.walk 400) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt400_north, advanceAt400_south, advanceAt426_south, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt374_south, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case654.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case654, memberCase654, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame654.bindings p
      intro binding member
      simp only [frame654, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h374
      · exact h400
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt400_north, advanceAt400_south, advanceAt426_south, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt374_south, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt400_north, advanceAt400_south, advanceAt426_south, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt374_south, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover746 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .east = some outcome) : OracleCovered rowCases746 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_east, advanceAt375_east, advanceAt375_west, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt374_east, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_east, advanceAt375_east, advanceAt375_west, advanceAt376_east, advanceAt377_east, advanceAt378_east, advanceAt379_east, advanceAt380_east, advanceAt381_east, advanceAt382_east, advanceAt383_east, advanceAt384_east, advanceAt385_east, advanceAt386_east, advanceAt387_east, advanceAt388_east, advanceAt389_east, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt376, doorAt376, trapAt376, boxAt376, holeAt376, floorAt377, doorAt377, trapAt377, boxAt377, holeAt377, floorAt378, doorAt378, trapAt378, boxAt378, holeAt378, floorAt379, doorAt379, trapAt379, boxAt379, holeAt379, floorAt380, doorAt380, trapAt380, boxAt380, holeAt380, floorAt381, doorAt381, trapAt381, boxAt381, holeAt381, floorAt382, doorAt382, trapAt382, boxAt382, holeAt382, floorAt383, doorAt383, trapAt383, boxAt383, holeAt383, floorAt384, doorAt384, trapAt384, boxAt384, holeAt384, floorAt385, doorAt385, trapAt385, boxAt385, holeAt385, floorAt386, doorAt386, trapAt386, boxAt386, holeAt386, floorAt387, doorAt387, trapAt387, boxAt387, holeAt387, floorAt388, doorAt388, trapAt388, boxAt388, holeAt388, floorAt389, doorAt389, trapAt389, boxAt389, holeAt389, cornerAt374_east, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover747 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .west = some outcome) : OracleCovered rowCases747 p outcome := by
  cases h374 : p 374 with
  | false =>
    cases h373 : p 373 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .west = some (.walk 373) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_west, advanceAt373_east, advanceAt373_west, advanceAt374_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_west, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case655.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case655, memberCase655, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame655.bindings p
      intro binding member
      simp only [frame655, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h373
      · exact h374
    | true =>
      cases h372 : p 372 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .west = some (.push 373 (.stay 372)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_west, advanceAt373_east, advanceAt373_west, advanceAt374_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_west, h372, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case861.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case861, memberCase861, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame861.bindings p
        intro binding member
        simp only [frame861, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h372
        · exact h373
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_west, advanceAt373_east, advanceAt373_west, advanceAt374_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_west, h372, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt364_west, advanceAt365_west, advanceAt366_west, advanceAt367_west, advanceAt368_west, advanceAt369_west, advanceAt370_west, advanceAt371_west, advanceAt372_west, advanceAt373_east, advanceAt373_west, advanceAt374_west, floorAt364, doorAt364, trapAt364, boxAt364, holeAt364, floorAt365, doorAt365, trapAt365, boxAt365, holeAt365, floorAt366, doorAt366, trapAt366, boxAt366, holeAt366, floorAt367, doorAt367, trapAt367, boxAt367, holeAt367, floorAt368, doorAt368, trapAt368, boxAt368, holeAt368, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_west, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover748 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .northEast = some outcome) : OracleCovered rowCases748 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_east, advanceAt374_northEast, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, cornerAt374_northEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_east, advanceAt374_northEast, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, cornerAt374_northEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover749 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .northWest = some outcome) : OracleCovered rowCases749 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_west, advanceAt374_northWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_northWest, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_north, advanceAt374_west, advanceAt374_northWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt374_northWest, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover750 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southEast = some outcome) : OracleCovered rowCases750 p outcome := by
  cases h374 : p 374 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_east, advanceAt374_southEast, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, cornerAt374_southEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_east, advanceAt374_southEast, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, cornerAt374_southEast, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover751 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southWest = some outcome) : OracleCovered rowCases751 p outcome := by
  cases h374 : p 374 with
  | false =>
    cases h400 : p 400 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southWest = some (.walk 399) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case656.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case656, memberCase656, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame656.bindings p
      intro binding member
      simp only [frame656, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h374
      · exact h400
    | true =>
      cases h373 : p 373 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southWest = some (.walk 399) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case657.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case657, memberCase657, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame657.bindings p
        intro binding member
        simp only [frame657, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h373
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 374 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt374_south, advanceAt374_west, advanceAt374_southWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt374_southWest, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover752 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .north = some outcome) : OracleCovered rowCases752 p outcome := by
  cases h370 : p 370 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .north = some (.walk 370) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt370_north, advanceAt370_south, advanceAt396_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case658.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case658, memberCase658, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame658.bindings p
    intro binding member
    simp only [frame658, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h370
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt32_north, advanceAt58_north, advanceAt84_north, advanceAt110_north, advanceAt136_north, advanceAt162_north, advanceAt188_north, advanceAt214_north, advanceAt240_north, advanceAt266_north, advanceAt292_north, advanceAt318_north, advanceAt344_north, advanceAt370_north, advanceAt370_south, advanceAt396_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, floorAt84, doorAt84, trapAt84, boxAt84, holeAt84, floorAt110, doorAt110, trapAt110, boxAt110, holeAt110, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt188, doorAt188, trapAt188, boxAt188, holeAt188, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_north, h370, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover753 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .south = some outcome) : OracleCovered rowCases753 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .south = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_south, advanceAt422_north, advanceAt422_south, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt422, doorAt422, trapAt422, boxAt422, holeAt422, cornerAt396_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover754 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .east = some outcome) : OracleCovered rowCases754 p outcome := by
  cases h397 : p 397 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .east = some (.walk 397) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_east, advanceAt397_east, advanceAt397_west, advanceAt398_east, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt396_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case659.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case659, memberCase659, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame659.bindings p
    intro binding member
    simp only [frame659, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h397
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt396_east, advanceAt397_east, advanceAt397_west, advanceAt398_east, advanceAt399_east, advanceAt400_east, advanceAt401_east, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt396_east, h397, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover755 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .west = some outcome) : OracleCovered rowCases755 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 5) p) (project (soko1_2.initial.holes.drop 5)) 396 .west = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_east, advanceAt395_west, advanceAt396_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, cornerAt396_west, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
end NetHack.Soko12Forward220.Unified.P05
