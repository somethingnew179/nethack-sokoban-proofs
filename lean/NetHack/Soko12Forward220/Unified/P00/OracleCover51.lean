import NetHack.Soko12Forward220.Unified.P00.OracleCover50
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P00
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover612 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northEast = some outcome) : OracleCovered rowCases612 p outcome := by
  cases h297 : p 297 with
  | false =>
    cases h271 : p 271 with
    | false =>
      cases h272 : p 272 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northEast = some (.walk 272) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_east, advanceAt297_northEast, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt297_northEast, h271, h272, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case581.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case581, memberCase581, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame581.bindings p
        intro binding member
        simp only [frame581, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h271
        · exact h272
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_east, advanceAt297_northEast, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt297_northEast, h271, h272, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_east, advanceAt297_northEast, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt297_northEast, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_east, advanceAt297_northEast, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, cornerAt297_northEast, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover613 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = some outcome) : OracleCovered rowCases613 p outcome := by
  cases h297 : p 297 with
  | false =>
    cases h271 : p 271 with
    | false =>
      cases h270 : p 270 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = some (.walk 270) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_west, advanceAt297_northWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_northWest, h270, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case582.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case582, memberCase582, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame582.bindings p
        intro binding member
        simp only [frame582, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h271
        · exact h297
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_west, advanceAt297_northWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_northWest, h270, h271, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h296 : p 296 with
      | false =>
        cases h270 : p 270 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = some (.walk 270) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_west, advanceAt297_northWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_northWest, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case583.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case583, memberCase583, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame583.bindings p
          intro binding member
          simp only [frame583, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h270
          · exact h296
          · exact h297
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_west, advanceAt297_northWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_northWest, h270, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_west, advanceAt297_northWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_northWest, h271, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_north, advanceAt297_west, advanceAt297_northWest, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, cornerAt297_northWest, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover614 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southEast = some outcome) : OracleCovered rowCases614 p outcome := by
  cases h297 : p 297 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt297_east, advanceAt297_southEast, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, cornerAt297_southEast, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt297_east, advanceAt297_southEast, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt298, doorAt298, trapAt298, boxAt298, holeAt298, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, cornerAt297_southEast, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover615 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southWest = some outcome) : OracleCovered rowCases615 p outcome := by
  cases h297 : p 297 with
  | false =>
    cases h296 : p 296 with
    | false =>
      cases h322 : p 322 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southWest = some (.walk 322) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt297_west, advanceAt297_southWest, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt297_southWest, h296, h297, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case584.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case584, memberCase584, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame584.bindings p
        intro binding member
        simp only [frame584, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h296
        · exact h297
        · exact h322
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt297_west, advanceAt297_southWest, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt297_southWest, h296, h297, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt297_west, advanceAt297_southWest, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt297_southWest, h296, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 297 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt297_south, advanceAt297_west, advanceAt297_southWest, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt297, doorAt297, trapAt297, boxAt297, holeAt297, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, cornerAt297_southWest, h297, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover616 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .north = some outcome) : OracleCovered rowCases616 p outcome := by
  cases h317 : p 317 with
  | false =>
    cases h291 : p 291 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .north = some (.walk 291) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt265_north, advanceAt291_north, advanceAt291_south, advanceAt317_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_north, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case585.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case585, memberCase585, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame585.bindings p
      intro binding member
      simp only [frame585, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h291
      · exact h317
    | true =>
      cases h265 : p 265 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .north = some (.push 291 (.stay 265)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt265_north, advanceAt291_north, advanceAt291_south, advanceAt317_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_north, h265, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case822.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case822, memberCase822, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame822.bindings p
        intro binding member
        simp only [frame822, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h265
        · exact h291
        · exact h317
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt265_north, advanceAt291_north, advanceAt291_south, advanceAt317_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_north, h265, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt265_north, advanceAt291_north, advanceAt291_south, advanceAt317_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_north, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover617 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .south = some outcome) : OracleCovered rowCases617 p outcome := by
  cases h317 : p 317 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_south, advanceAt343_north, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt317_south, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_south, advanceAt343_north, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt317_south, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover618 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .east = some outcome) : OracleCovered rowCases618 p outcome := by
  cases h317 : p 317 with
  | false =>
    cases h318 : p 318 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .east = some (.walk 318) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_east, advanceAt318_east, advanceAt318_west, advanceAt319_east, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt317_east, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case586.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case586, memberCase586, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame586.bindings p
      intro binding member
      simp only [frame586, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h317
      · exact h318
    | true =>
      cases h319 : p 319 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .east = some (.push 318 (.stay 319)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_east, advanceAt318_east, advanceAt318_west, advanceAt319_east, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt317_east, h317, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case832.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case832, memberCase832, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame832.bindings p
        intro binding member
        simp only [frame832, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h317
        · exact h318
        · exact h319
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_east, advanceAt318_east, advanceAt318_west, advanceAt319_east, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt317_east, h317, h318, h319, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_east, advanceAt318_east, advanceAt318_west, advanceAt319_east, advanceAt320_east, advanceAt321_east, advanceAt322_east, advanceAt323_east, advanceAt324_east, advanceAt325_east, advanceAt326_east, advanceAt327_east, advanceAt328_east, advanceAt329_east, advanceAt330_east, advanceAt331_east, advanceAt332_east, advanceAt333_east, advanceAt334_east, advanceAt335_east, advanceAt336_east, advanceAt337_east, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt324, doorAt324, trapAt324, boxAt324, holeAt324, floorAt325, doorAt325, trapAt325, boxAt325, holeAt325, floorAt326, doorAt326, trapAt326, boxAt326, holeAt326, floorAt327, doorAt327, trapAt327, boxAt327, holeAt327, floorAt328, doorAt328, trapAt328, boxAt328, holeAt328, floorAt329, doorAt329, trapAt329, boxAt329, holeAt329, floorAt330, doorAt330, trapAt330, boxAt330, holeAt330, floorAt331, doorAt331, trapAt331, boxAt331, holeAt331, floorAt332, doorAt332, trapAt332, boxAt332, holeAt332, floorAt333, doorAt333, trapAt333, boxAt333, holeAt333, floorAt334, doorAt334, trapAt334, boxAt334, holeAt334, floorAt335, doorAt335, trapAt335, boxAt335, holeAt335, floorAt336, doorAt336, trapAt336, boxAt336, holeAt336, floorAt337, doorAt337, trapAt337, boxAt337, holeAt337, cornerAt317_east, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover619 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .west = some outcome) : OracleCovered rowCases619 p outcome := by
  cases h317 : p 317 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_east, advanceAt316_west, advanceAt317_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_west, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt312_west, advanceAt313_west, advanceAt314_west, advanceAt315_west, advanceAt316_east, advanceAt316_west, advanceAt317_west, floorAt312, doorAt312, trapAt312, boxAt312, holeAt312, floorAt313, doorAt313, trapAt313, boxAt313, holeAt313, floorAt314, doorAt314, trapAt314, boxAt314, holeAt314, floorAt315, doorAt315, trapAt315, boxAt315, holeAt315, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_west, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover620 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = some outcome) : OracleCovered rowCases620 p outcome := by
  cases h317 : p 317 with
  | false =>
    cases h291 : p 291 with
    | false =>
      cases h292 : p 292 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = some (.walk 292) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_east, advanceAt317_northEast, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt317_northEast, h291, h292, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case587.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case587, memberCase587, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame587.bindings p
        intro binding member
        simp only [frame587, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h291
        · exact h292
        · exact h317
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_east, advanceAt317_northEast, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt317_northEast, h291, h292, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h318 : p 318 with
      | false =>
        cases h292 : p 292 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = some (.walk 292) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_east, advanceAt317_northEast, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt317_northEast, h291, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case588.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case588, memberCase588, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame588.bindings p
          intro binding member
          simp only [frame588, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h292
          · exact h317
          · exact h318
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_east, advanceAt317_northEast, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt317_northEast, h291, h292, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_east, advanceAt317_northEast, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt317_northEast, h291, h317, h318, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_east, advanceAt317_northEast, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, cornerAt317_northEast, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover621 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northWest = some outcome) : OracleCovered rowCases621 p outcome := by
  cases h317 : p 317 with
  | false =>
    cases h291 : p 291 with
    | false =>
      cases h290 : p 290 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northWest = some (.walk 290) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_west, advanceAt317_northWest, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_northWest, h290, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case589.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case589, memberCase589, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame589.bindings p
        intro binding member
        simp only [frame589, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h290
        · exact h291
        · exact h317
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_west, advanceAt317_northWest, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_northWest, h290, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_west, advanceAt317_northWest, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_northWest, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_north, advanceAt317_west, advanceAt317_northWest, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, cornerAt317_northWest, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover622 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .southEast = some outcome) : OracleCovered rowCases622 p outcome := by
  cases h317 : p 317 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_south, advanceAt317_east, advanceAt317_southEast, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, cornerAt317_southEast, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_south, advanceAt317_east, advanceAt317_southEast, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, cornerAt317_southEast, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover623 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .southWest = some outcome) : OracleCovered rowCases623 p outcome := by
  cases h317 : p 317 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_south, advanceAt317_west, advanceAt317_southWest, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, cornerAt317_southWest, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 0) p) (project (soko1_2.initial.holes.drop 0)) 317 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt317_south, advanceAt317_west, advanceAt317_southWest, floorAt316, doorAt316, trapAt316, boxAt316, holeAt316, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, cornerAt317_southWest, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P00
