import NetHack.Soko12Forward220.Unified.P04.OracleCover13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover168 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .north = some outcome) : OracleCovered rowCases168 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt114_south, advanceAt140_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_north, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt114_south, advanceAt140_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_north, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover169 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .south = some outcome) : OracleCovered rowCases169 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h166 : p 166 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .south = some (.walk 166) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case099.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case099, memberCase099, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame099.bindings p
      intro binding member
      simp only [frame099, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h140
      · exact h166
    | true =>
      cases h192 : p 192 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .south = some (.push 166 (.stay 192)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, h166, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case719.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case719, memberCase719, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame719.bindings p
        intro binding member
        simp only [frame719, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h166
        · exact h192
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, h166, h192, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt166_north, advanceAt166_south, advanceAt192_south, advanceAt218_south, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt140_south, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover170 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .east = some outcome) : OracleCovered rowCases170 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h141 : p 141 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .east = some (.walk 141) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case100.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case100, memberCase100, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame100.bindings p
      intro binding member
      simp only [frame100, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h140
      · exact h141
    | true =>
      cases h142 : p 142 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .east = some (.push 141 (.stay 142)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case696.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case696, memberCase696, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame696.bindings p
        intro binding member
        simp only [frame696, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h141
        · exact h142
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_east, advanceAt141_east, advanceAt141_west, advanceAt142_east, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt140_east, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover171 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .west = some outcome) : OracleCovered rowCases171 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_east, advanceAt139_west, advanceAt140_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_west, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_east, advanceAt139_west, advanceAt140_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_west, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover172 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northEast = some outcome) : OracleCovered rowCases172 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h141 : p 141 with
    | false =>
      cases h115 : p 115 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northEast = some (.walk 115) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h115, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case101.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case101, memberCase101, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame101.bindings p
        intro binding member
        simp only [frame101, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h115
        · exact h140
        · exact h141
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h115, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_east, advanceAt140_northEast, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt140_northEast, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover173 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northWest = some outcome) : OracleCovered rowCases173 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_west, advanceAt140_northWest, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_northWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_north, advanceAt140_west, advanceAt140_northWest, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, cornerAt140_northWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover174 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = some outcome) : OracleCovered rowCases174 p outcome := by
  cases h140 : p 140 with
  | false =>
    cases h166 : p 166 with
    | false =>
      cases h167 : p 167 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = some (.walk 167) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case102.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case102, memberCase102, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame102.bindings p
        intro binding member
        simp only [frame102, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h140
        · exact h166
        · exact h167
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h141 : p 141 with
      | false =>
        cases h167 : p 167 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = some (.walk 167) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case103.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case103, memberCase103, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame103.bindings p
          intro binding member
          simp only [frame103, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h140
          · exact h141
          · exact h167
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h141, h166, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, h141, h166, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_east, advanceAt140_southEast, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, cornerAt140_southEast, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover175 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southWest = some outcome) : OracleCovered rowCases175 p outcome := by
  cases h140 : p 140 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_west, advanceAt140_southWest, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, cornerAt140_southWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 140 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt140_south, advanceAt140_west, advanceAt140_southWest, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt165, doorAt165, trapAt165, boxAt165, holeAt165, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, cornerAt140_southWest, h140, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover176 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .north = some outcome) : OracleCovered rowCases176 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h115 : p 115 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .north = some (.walk 115) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt115_south, advanceAt141_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_north, h115, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case104.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case104, memberCase104, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame104.bindings p
      intro binding member
      simp only [frame104, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h115
      · exact h141
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .north = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt115_south, advanceAt141_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_north, h115, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt115_south, advanceAt141_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_north, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover177 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .south = some outcome) : OracleCovered rowCases177 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h167 : p 167 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .south = some (.walk 167) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt167_north, advanceAt167_south, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt141_south, h141, h167, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case105.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case105, memberCase105, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame105.bindings p
      intro binding member
      simp only [frame105, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h141
      · exact h167
    | true =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .south = some (.push 167 (.stay 193)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt167_north, advanceAt167_south, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt141_south, h141, h167, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case721.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case721, memberCase721, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame721.bindings p
        intro binding member
        simp only [frame721, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h141
        · exact h167
        · exact h193
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt167_north, advanceAt167_south, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt141_south, h141, h167, h193, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_south, advanceAt167_north, advanceAt167_south, advanceAt193_south, advanceAt219_south, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt141_south, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover178 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .east = some outcome) : OracleCovered rowCases178 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h142 : p 142 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .east = some (.walk 142) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_east, advanceAt142_east, advanceAt142_west, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt141_east, h141, h142, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case106.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case106, memberCase106, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame106.bindings p
      intro binding member
      simp only [frame106, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h141
      · exact h142
    | true =>
      cases h143 : p 143 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .east = some (.push 142 (.stay 143)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_east, advanceAt142_east, advanceAt142_west, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt141_east, h141, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case700.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case700, memberCase700, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame700.bindings p
        intro binding member
        simp only [frame700, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h141
        · exact h142
        · exact h143
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_east, advanceAt142_east, advanceAt142_west, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt141_east, h141, h142, h143, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt141_east, advanceAt142_east, advanceAt142_west, advanceAt143_east, advanceAt144_east, advanceAt145_east, advanceAt146_east, advanceAt147_east, advanceAt148_east, advanceAt149_east, advanceAt150_east, advanceAt151_east, advanceAt152_east, advanceAt153_east, advanceAt154_east, advanceAt155_east, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt142, doorAt142, trapAt142, boxAt142, holeAt142, floorAt143, doorAt143, trapAt143, boxAt143, holeAt143, floorAt144, doorAt144, trapAt144, boxAt144, holeAt144, floorAt145, doorAt145, trapAt145, boxAt145, holeAt145, floorAt146, doorAt146, trapAt146, boxAt146, holeAt146, floorAt147, doorAt147, trapAt147, boxAt147, holeAt147, floorAt148, doorAt148, trapAt148, boxAt148, holeAt148, floorAt149, doorAt149, trapAt149, boxAt149, holeAt149, floorAt150, doorAt150, trapAt150, boxAt150, holeAt150, floorAt151, doorAt151, trapAt151, boxAt151, holeAt151, floorAt152, doorAt152, trapAt152, boxAt152, holeAt152, floorAt153, doorAt153, trapAt153, boxAt153, holeAt153, floorAt154, doorAt154, trapAt154, boxAt154, holeAt154, floorAt155, doorAt155, trapAt155, boxAt155, holeAt155, cornerAt141_east, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover179 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .west = some outcome) : OracleCovered rowCases179 p outcome := by
  cases h141 : p 141 with
  | false =>
    cases h140 : p 140 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .west = some (.walk 140) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_east, advanceAt140_west, advanceAt141_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_west, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case107.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case107, memberCase107, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame107.bindings p
      intro binding member
      simp only [frame107, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h140
      · exact h141
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_east, advanceAt140_west, advanceAt141_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_west, h140, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 141 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt130_west, advanceAt131_west, advanceAt132_west, advanceAt133_west, advanceAt134_west, advanceAt135_west, advanceAt136_west, advanceAt137_west, advanceAt138_west, advanceAt139_west, advanceAt140_east, advanceAt140_west, advanceAt141_west, floorAt130, doorAt130, trapAt130, boxAt130, holeAt130, floorAt131, doorAt131, trapAt131, boxAt131, holeAt131, floorAt132, doorAt132, trapAt132, boxAt132, holeAt132, floorAt133, doorAt133, trapAt133, boxAt133, holeAt133, floorAt134, doorAt134, trapAt134, boxAt134, holeAt134, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt136, doorAt136, trapAt136, boxAt136, holeAt136, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, cornerAt141_west, h141, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
