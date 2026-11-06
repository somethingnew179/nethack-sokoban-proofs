import NetHack.Soko12Forward220.Unified.P02.OracleCover33
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover408 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .north = some outcome) : OracleCovered rowCases408 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h192 : p 192 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .north = some (.walk 192) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case370.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case370, memberCase370, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame370.bindings p
      intro binding member
      simp only [frame370, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h192
      · exact h218
    | true =>
      cases h166 : p 166 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .north = some (.push 192 (.stay 166)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h166, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case744.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case744, memberCase744, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame744.bindings p
        intro binding member
        simp only [frame744, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h166
        · exact h192
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h166, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt192_south, advanceAt218_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_north, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover409 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .south = some outcome) : OracleCovered rowCases409 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h244 : p 244 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .south = some (.walk 244) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case371.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case371, memberCase371, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame371.bindings p
      intro binding member
      simp only [frame371, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h218
      · exact h244
    | true =>
      cases h270 : p 270 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .south = some (.push 244 (.stay 270)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case797.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case797, memberCase797, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame797.bindings p
        intro binding member
        simp only [frame797, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h244
        · exact h270
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt244_north, advanceAt244_south, advanceAt270_south, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt218_south, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover410 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .east = some outcome) : OracleCovered rowCases410 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h219 : p 219 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .east = some (.walk 219) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case372.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case372, memberCase372, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame372.bindings p
      intro binding member
      simp only [frame372, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h218
      · exact h219
    | true =>
      cases h220 : p 220 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .east = some (.push 219 (.stay 220)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case780.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case780, memberCase780, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame780.bindings p
        intro binding member
        simp only [frame780, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h219
        · exact h220
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_east, advanceAt219_east, advanceAt219_west, advanceAt220_east, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt218_east, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover411 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .west = some outcome) : OracleCovered rowCases411 p outcome := by
  cases h218 : p 218 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_east, advanceAt217_west, advanceAt218_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_west, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_east, advanceAt217_west, advanceAt218_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_west, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover412 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = some outcome) : OracleCovered rowCases412 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h193 : p 193 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = some (.walk 193) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case373.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case373, memberCase373, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame373.bindings p
        intro binding member
        simp only [frame373, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h192
        · exact h193
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h219 : p 219 with
      | false =>
        cases h193 : p 193 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = some (.walk 193) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case374.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case374, memberCase374, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame374.bindings p
          intro binding member
          simp only [frame374, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h193
          · exact h218
          · exact h219
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h193, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h192, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_east, advanceAt218_northEast, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt218_northEast, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover413 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northWest = some outcome) : OracleCovered rowCases413 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h192 : p 192 with
    | false =>
      cases h191 : p 191 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northWest = some (.walk 191) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h191, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case375.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case375, memberCase375, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame375.bindings p
        intro binding member
        simp only [frame375, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h191
        · exact h192
        · exact h218
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h191, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h192, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_north, advanceAt218_west, advanceAt218_northWest, floorAt191, doorAt191, trapAt191, boxAt191, holeAt191, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, cornerAt218_northWest, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover414 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = some outcome) : OracleCovered rowCases414 p outcome := by
  cases h218 : p 218 with
  | false =>
    cases h244 : p 244 with
    | false =>
      cases h245 : p 245 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = some (.walk 245) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case376.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case376, memberCase376, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame376.bindings p
        intro binding member
        simp only [frame376, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h244
        · exact h245
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h219 : p 219 with
      | false =>
        cases h245 : p 245 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = some (.walk 245) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case377.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case377, memberCase377, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame377.bindings p
          intro binding member
          simp only [frame377, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h218
          · exact h219
          · exact h245
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h219, h244, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, h219, h244, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_east, advanceAt218_southEast, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, cornerAt218_southEast, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover415 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southWest = some outcome) : OracleCovered rowCases415 p outcome := by
  cases h218 : p 218 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_west, advanceAt218_southWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt218_southWest, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 218 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt218_south, advanceAt218_west, advanceAt218_southWest, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt243, doorAt243, trapAt243, boxAt243, holeAt243, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, cornerAt218_southWest, h218, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover416 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .north = some outcome) : OracleCovered rowCases416 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h193 : p 193 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .north = some (.walk 193) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt193_south, advanceAt219_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_north, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case378.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case378, memberCase378, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame378.bindings p
      intro binding member
      simp only [frame378, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h193
      · exact h219
    | true =>
      cases h167 : p 167 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .north = some (.push 193 (.stay 167)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt193_south, advanceAt219_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_north, h167, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case748.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case748, memberCase748, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame748.bindings p
        intro binding member
        simp only [frame748, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h167
        · exact h193
        · exact h219
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt193_south, advanceAt219_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_north, h167, h193, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt11_north, advanceAt37_north, advanceAt63_north, advanceAt89_north, advanceAt115_north, advanceAt141_north, advanceAt167_north, advanceAt193_north, advanceAt193_south, advanceAt219_north, floorAt11, doorAt11, trapAt11, boxAt11, holeAt11, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt63, doorAt63, trapAt63, boxAt63, holeAt63, floorAt89, doorAt89, trapAt89, boxAt89, holeAt89, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt141, doorAt141, trapAt141, boxAt141, holeAt141, floorAt167, doorAt167, trapAt167, boxAt167, holeAt167, floorAt193, doorAt193, trapAt193, boxAt193, holeAt193, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_north, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover417 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .south = some outcome) : OracleCovered rowCases417 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h245 : p 245 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .south = some (.walk 245) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt245_north, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt219_south, h219, h245, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case379.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case379, memberCase379, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame379.bindings p
      intro binding member
      simp only [frame379, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h219
      · exact h245
    | true =>
      cases h271 : p 271 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .south = some (.push 245 (.stay 271)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt245_north, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt219_south, h219, h245, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case799.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case799, memberCase799, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame799.bindings p
        intro binding member
        simp only [frame799, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h219
        · exact h245
        · exact h271
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt245_north, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt219_south, h219, h245, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_south, advanceAt245_north, advanceAt245_south, advanceAt271_south, advanceAt297_south, advanceAt323_south, advanceAt349_south, advanceAt375_south, advanceAt401_south, advanceAt427_south, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt219_south, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover418 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .east = some outcome) : OracleCovered rowCases418 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h220 : p 220 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .east = some (.walk 220) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_east, advanceAt220_east, advanceAt220_west, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt219_east, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case380.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case380, memberCase380, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame380.bindings p
      intro binding member
      simp only [frame380, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h219
      · exact h220
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_east, advanceAt220_east, advanceAt220_west, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt219_east, h219, h220, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt219_east, advanceAt220_east, advanceAt220_west, advanceAt221_east, advanceAt222_east, advanceAt223_east, advanceAt224_east, advanceAt225_east, advanceAt226_east, advanceAt227_east, advanceAt228_east, advanceAt229_east, advanceAt230_east, advanceAt231_east, advanceAt232_east, advanceAt233_east, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, floorAt220, doorAt220, trapAt220, boxAt220, holeAt220, floorAt221, doorAt221, trapAt221, boxAt221, holeAt221, floorAt222, doorAt222, trapAt222, boxAt222, holeAt222, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt224, doorAt224, trapAt224, boxAt224, holeAt224, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt229, doorAt229, trapAt229, boxAt229, holeAt229, floorAt230, doorAt230, trapAt230, boxAt230, holeAt230, floorAt231, doorAt231, trapAt231, boxAt231, holeAt231, floorAt232, doorAt232, trapAt232, boxAt232, holeAt232, floorAt233, doorAt233, trapAt233, boxAt233, holeAt233, cornerAt219_east, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover419 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .west = some outcome) : OracleCovered rowCases419 p outcome := by
  cases h219 : p 219 with
  | false =>
    cases h218 : p 218 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .west = some (.walk 218) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_east, advanceAt218_west, advanceAt219_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_west, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case381.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case381, memberCase381, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame381.bindings p
      intro binding member
      simp only [frame381, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h218
      · exact h219
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_east, advanceAt218_west, advanceAt219_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_west, h218, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 219 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt208_west, advanceAt209_west, advanceAt210_west, advanceAt211_west, advanceAt212_west, advanceAt213_west, advanceAt214_west, advanceAt215_west, advanceAt216_west, advanceAt217_west, advanceAt218_east, advanceAt218_west, advanceAt219_west, floorAt208, doorAt208, trapAt208, boxAt208, holeAt208, floorAt209, doorAt209, trapAt209, boxAt209, holeAt209, floorAt210, doorAt210, trapAt210, boxAt210, holeAt210, floorAt211, doorAt211, trapAt211, boxAt211, holeAt211, floorAt212, doorAt212, trapAt212, boxAt212, holeAt212, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt214, doorAt214, trapAt214, boxAt214, holeAt214, floorAt215, doorAt215, trapAt215, boxAt215, holeAt215, floorAt216, doorAt216, trapAt216, boxAt216, holeAt216, floorAt217, doorAt217, trapAt217, boxAt217, holeAt217, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt219, doorAt219, trapAt219, boxAt219, holeAt219, cornerAt219_west, h219, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P02
