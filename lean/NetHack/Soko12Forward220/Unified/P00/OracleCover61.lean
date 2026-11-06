import NetHack.Soko12Forward220.Unified.P00.OracleCover60
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover732 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northEast = some outcome) : OracleCovered rowCases732 p outcome := by
  cases h373 : p 373 with
  | false =>
    cases h374 : p 374 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northEast = some (.walk 374) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_east, advanceAt399_northEast, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt399_northEast, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case658.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case658, memberCase658, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame658.bindings p
      intro binding member
      simp only [frame658, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h373
      · exact h374
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_east, advanceAt399_northEast, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt399_northEast, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    cases h400 : p 400 with
    | false =>
      cases h374 : p 374 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northEast = some (.walk 374) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_east, advanceAt399_northEast, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt399_northEast, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case659.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case659, memberCase659, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame659.bindings p
        intro binding member
        simp only [frame659, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h374
        · exact h400
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_east, advanceAt399_northEast, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt399_northEast, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_east, advanceAt399_northEast, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt399_northEast, h373, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
theorem oracleCover733 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northWest = some outcome) : OracleCovered rowCases733 p outcome := by
  cases h373 : p 373 with
  | false =>
    cases h372 : p 372 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northWest = some (.walk 372) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_west, advanceAt399_northWest, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, cornerAt399_northWest, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case660.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case660, memberCase660, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame660.bindings p
      intro binding member
      simp only [frame660, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h372
      · exact h373
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_west, advanceAt399_northWest, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, cornerAt399_northWest, h372, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_north, advanceAt399_west, advanceAt399_northWest, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, cornerAt399_northWest, h373, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover734 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .southEast = some outcome) : OracleCovered rowCases734 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_south, advanceAt399_east, advanceAt399_southEast, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt399_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover735 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .southWest = some outcome) : OracleCovered rowCases735 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 399 .southWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt399_south, advanceAt399_west, advanceAt399_southWest, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt424, doorAt424, trapAt424, boxAt424, holeAt424, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, cornerAt399_southWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover736 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .north = some outcome) : OracleCovered rowCases736 p outcome := by
  cases h400 : p 400 with
  | false =>
    cases h374 : p 374 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .north = some (.walk 374) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt374_north, advanceAt374_south, advanceAt400_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_north, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case661.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case661, memberCase661, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame661.bindings p
      intro binding member
      simp only [frame661, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h374
      · exact h400
    | true =>
      cases h348 : p 348 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .north = some (.push 374 (.stay 348)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt374_north, advanceAt374_south, advanceAt400_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_north, h348, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case852.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case852, memberCase852, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame852.bindings p
        intro binding member
        simp only [frame852, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h348
        · exact h374
        · exact h400
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt374_north, advanceAt374_south, advanceAt400_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_north, h348, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt348_north, advanceAt374_north, advanceAt374_south, advanceAt400_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_north, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover737 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .south = some outcome) : OracleCovered rowCases737 p outcome := by
  cases h400 : p 400 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_south, advanceAt426_north, advanceAt426_south, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt400_south, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_south, advanceAt426_north, advanceAt426_south, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt400_south, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover738 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .east = some outcome) : OracleCovered rowCases738 p outcome := by
  cases h400 : p 400 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_east, advanceAt401_east, advanceAt401_west, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt400_east, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_east, advanceAt401_east, advanceAt401_west, advanceAt402_east, advanceAt403_east, advanceAt404_east, advanceAt405_east, advanceAt406_east, advanceAt407_east, advanceAt408_east, advanceAt409_east, advanceAt410_east, advanceAt411_east, advanceAt412_east, advanceAt413_east, advanceAt414_east, advanceAt415_east, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt402, doorAt402, trapAt402, boxAt402, holeAt402, floorAt403, doorAt403, trapAt403, boxAt403, holeAt403, floorAt404, doorAt404, trapAt404, boxAt404, holeAt404, floorAt405, doorAt405, trapAt405, boxAt405, holeAt405, floorAt406, doorAt406, trapAt406, boxAt406, holeAt406, floorAt407, doorAt407, trapAt407, boxAt407, holeAt407, floorAt408, doorAt408, trapAt408, boxAt408, holeAt408, floorAt409, doorAt409, trapAt409, boxAt409, holeAt409, floorAt410, doorAt410, trapAt410, boxAt410, holeAt410, floorAt411, doorAt411, trapAt411, boxAt411, holeAt411, floorAt412, doorAt412, trapAt412, boxAt412, holeAt412, floorAt413, doorAt413, trapAt413, boxAt413, holeAt413, floorAt414, doorAt414, trapAt414, boxAt414, holeAt414, floorAt415, doorAt415, trapAt415, boxAt415, holeAt415, cornerAt400_east, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover739 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .west = some outcome) : OracleCovered rowCases739 p outcome := by
  cases h400 : p 400 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .west = some (.walk 399) := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_west, advanceAt396_west, advanceAt397_west, advanceAt398_west, advanceAt399_east, advanceAt399_west, advanceAt400_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_west, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case662.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case662, memberCase662, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame662.bindings p
    intro binding member
    simp only [frame662, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h400
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt390_west, advanceAt391_west, advanceAt392_west, advanceAt393_west, advanceAt394_west, advanceAt395_west, advanceAt396_west, advanceAt397_west, advanceAt398_west, advanceAt399_east, advanceAt399_west, advanceAt400_west, floorAt390, doorAt390, trapAt390, boxAt390, holeAt390, floorAt391, doorAt391, trapAt391, boxAt391, holeAt391, floorAt392, doorAt392, trapAt392, boxAt392, holeAt392, floorAt393, doorAt393, trapAt393, boxAt393, holeAt393, floorAt394, doorAt394, trapAt394, boxAt394, holeAt394, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt396, doorAt396, trapAt396, boxAt396, holeAt396, floorAt397, doorAt397, trapAt397, boxAt397, holeAt397, floorAt398, doorAt398, trapAt398, boxAt398, holeAt398, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_west, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover740 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northEast = some outcome) : OracleCovered rowCases740 p outcome := by
  cases h400 : p 400 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_east, advanceAt400_northEast, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, cornerAt400_northEast, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_east, advanceAt400_northEast, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, cornerAt400_northEast, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover741 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northWest = some outcome) : OracleCovered rowCases741 p outcome := by
  cases h400 : p 400 with
  | false =>
    cases h374 : p 374 with
    | false =>
      cases h373 : p 373 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northWest = some (.walk 373) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_west, advanceAt400_northWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_northWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case663.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case663, memberCase663, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame663.bindings p
        intro binding member
        simp only [frame663, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h373
        · exact h400
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_west, advanceAt400_northWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_northWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h373 : p 373 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northWest = some (.walk 373) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_west, advanceAt400_northWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_northWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case663.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case663, memberCase663, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame663.bindings p
        intro binding member
        simp only [frame663, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h373
        · exact h400
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_west, advanceAt400_northWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_northWest, h373, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_north, advanceAt400_west, advanceAt400_northWest, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, cornerAt400_northWest, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover742 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .southEast = some outcome) : OracleCovered rowCases742 p outcome := by
  cases h400 : p 400 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_south, advanceAt400_east, advanceAt400_southEast, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt400_southEast, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_south, advanceAt400_east, advanceAt400_southEast, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt401, doorAt401, trapAt401, boxAt401, holeAt401, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, floorAt427, doorAt427, trapAt427, boxAt427, holeAt427, cornerAt400_southEast, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover743 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .southWest = some outcome) : OracleCovered rowCases743 p outcome := by
  cases h400 : p 400 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_south, advanceAt400_west, advanceAt400_southWest, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt400_southWest, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 400 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt400_south, advanceAt400_west, advanceAt400_southWest, floorAt399, doorAt399, trapAt399, boxAt399, holeAt399, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt425, doorAt425, trapAt425, boxAt425, holeAt425, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt400_southWest, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
