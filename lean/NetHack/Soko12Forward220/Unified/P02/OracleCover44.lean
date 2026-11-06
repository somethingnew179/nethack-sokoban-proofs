import NetHack.Soko12Forward220.Unified.P02.OracleCover43
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P02
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover528 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .north = some outcome) : OracleCovered rowCases528 p outcome := by
  cases h265 : p 265 with
  | false =>
    cases h239 : p 239 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .north = some (.walk 239) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt239_south, advanceAt265_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_north, h239, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case502.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case502, memberCase502, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame502.bindings p
      intro binding member
      simp only [frame502, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h239
      · exact h265
    | true =>
      cases h213 : p 213 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .north = some (.push 239 (.stay 213)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt239_south, advanceAt265_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_north, h213, h239, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case794.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case794, memberCase794, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame794.bindings p
        intro binding member
        simp only [frame794, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h213
        · exact h239
        · exact h265
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt239_south, advanceAt265_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_north, h213, h239, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt31_north, advanceAt57_north, advanceAt83_north, advanceAt109_north, advanceAt135_north, advanceAt161_north, advanceAt187_north, advanceAt213_north, advanceAt239_north, advanceAt239_south, advanceAt265_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_north, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover529 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .south = some outcome) : OracleCovered rowCases529 p outcome := by
  cases h265 : p 265 with
  | false =>
    cases h291 : p 291 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .south = some (.walk 291) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt291_north, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt265_south, h265, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case503.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case503, memberCase503, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame503.bindings p
      intro binding member
      simp only [frame503, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h265
      · exact h291
    | true =>
      cases h317 : p 317 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .south = some (.push 291 (.stay 317)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt291_north, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt265_south, h265, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case827.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case827, memberCase827, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame827.bindings p
        intro binding member
        simp only [frame827, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h265
        · exact h291
        · exact h317
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt291_north, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt265_south, h265, h291, h317, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt291_north, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt265_south, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover530 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .east = some outcome) : OracleCovered rowCases530 p outcome := by
  cases h265 : p 265 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_east, advanceAt266_east, advanceAt266_west, advanceAt267_east, advanceAt268_east, advanceAt269_east, advanceAt270_east, advanceAt271_east, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt265_east, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_east, advanceAt266_east, advanceAt266_west, advanceAt267_east, advanceAt268_east, advanceAt269_east, advanceAt270_east, advanceAt271_east, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt265_east, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover531 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .west = some outcome) : OracleCovered rowCases531 p outcome := by
  cases h265 : p 265 with
  | false =>
    cases h264 : p 264 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .west = some (.walk 264) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_east, advanceAt264_west, advanceAt265_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_west, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case504.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case504, memberCase504, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame504.bindings p
      intro binding member
      simp only [frame504, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h264
      · exact h265
    | true =>
      cases h263 : p 263 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .west = some (.push 264 (.stay 263)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_east, advanceAt264_west, advanceAt265_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_west, h263, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case813.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case813, memberCase813, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame813.bindings p
        intro binding member
        simp only [frame813, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h263
        · exact h264
        · exact h265
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_east, advanceAt264_west, advanceAt265_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_west, h263, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_east, advanceAt264_west, advanceAt265_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_west, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover532 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northEast = some outcome) : OracleCovered rowCases532 p outcome := by
  cases h265 : p 265 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_east, advanceAt265_northEast, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, cornerAt265_northEast, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_east, advanceAt265_northEast, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt240, doorAt240, trapAt240, boxAt240, holeAt240, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, cornerAt265_northEast, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover533 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = some outcome) : OracleCovered rowCases533 p outcome := by
  cases h265 : p 265 with
  | false =>
    cases h239 : p 239 with
    | false =>
      cases h238 : p 238 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = some (.walk 238) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_west, advanceAt265_northWest, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_northWest, h238, h239, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case505.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case505, memberCase505, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame505.bindings p
        intro binding member
        simp only [frame505, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h238
        · exact h239
        · exact h265
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_west, advanceAt265_northWest, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_northWest, h238, h239, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h264 : p 264 with
      | false =>
        cases h238 : p 238 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = some (.walk 238) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_west, advanceAt265_northWest, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_northWest, h238, h239, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case506.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case506, memberCase506, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame506.bindings p
          intro binding member
          simp only [frame506, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h238
          · exact h264
          · exact h265
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_west, advanceAt265_northWest, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_northWest, h238, h239, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_west, advanceAt265_northWest, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_northWest, h239, h264, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_north, advanceAt265_west, advanceAt265_northWest, floorAt238, doorAt238, trapAt238, boxAt238, holeAt238, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, cornerAt265_northWest, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover534 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southEast = some outcome) : OracleCovered rowCases534 p outcome := by
  cases h265 : p 265 with
  | false =>
    cases h291 : p 291 with
    | false =>
      cases h292 : p 292 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southEast = some (.walk 292) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_east, advanceAt265_southEast, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt265_southEast, h265, h291, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case507.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case507, memberCase507, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame507.bindings p
        intro binding member
        simp only [frame507, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h265
        · exact h291
        · exact h292
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_east, advanceAt265_southEast, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt265_southEast, h265, h291, h292, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_east, advanceAt265_southEast, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt265_southEast, h265, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_east, advanceAt265_southEast, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt292, doorAt292, trapAt292, boxAt292, holeAt292, cornerAt265_southEast, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover535 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = some outcome) : OracleCovered rowCases535 p outcome := by
  cases h265 : p 265 with
  | false =>
    cases h291 : p 291 with
    | false =>
      cases h290 : p 290 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = some (.walk 290) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_west, advanceAt265_southWest, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt265_southWest, h265, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case508.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case508, memberCase508, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame508.bindings p
        intro binding member
        simp only [frame508, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h265
        · exact h290
        · exact h291
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_west, advanceAt265_southWest, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt265_southWest, h265, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h264 : p 264 with
      | false =>
        cases h290 : p 290 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = some (.walk 290) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_west, advanceAt265_southWest, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt265_southWest, h264, h265, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = case509.outcome := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨case509, memberCase509, same, ?_⟩
          change DecisionDAGTransform.Satisfies frame509.bindings p
          intro binding member
          simp only [frame509, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact h264
          · exact h265
          · exact h290
        | true =>
          have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_west, advanceAt265_southWest, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt265_southWest, h264, h265, h290, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_west, advanceAt265_southWest, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt265_southWest, h264, h265, h291, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 265 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt265_south, advanceAt265_west, advanceAt265_southWest, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt290, doorAt290, trapAt290, boxAt290, holeAt290, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, cornerAt265_southWest, h265, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover536 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .north = some outcome) : OracleCovered rowCases536 p outcome := by
  cases h270 : p 270 with
  | false =>
    cases h244 : p 244 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .north = some (.walk 244) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt244_south, advanceAt270_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt270_north, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case510.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case510, memberCase510, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame510.bindings p
      intro binding member
      simp only [frame510, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h244
      · exact h270
    | true =>
      cases h218 : p 218 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .north = some (.push 244 (.stay 218)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt244_south, advanceAt270_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt270_north, h218, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case796.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case796, memberCase796, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame796.bindings p
        intro binding member
        simp only [frame796, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h218
        · exact h244
        · exact h270
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt244_south, advanceAt270_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt270_north, h218, h244, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt244_south, advanceAt270_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt270_north, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover537 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .south = some outcome) : OracleCovered rowCases537 p outcome := by
  cases h270 : p 270 with
  | false =>
    cases h296 : p 296 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .south = some (.walk 296) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_south, advanceAt296_north, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt270_south, h270, h296, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case511.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case511, memberCase511, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame511.bindings p
      intro binding member
      simp only [frame511, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h270
      · exact h296
    | true =>
      cases h322 : p 322 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .south = some (.push 296 (.stay 322)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_south, advanceAt296_north, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt270_south, h270, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case835.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case835, memberCase835, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame835.bindings p
        intro binding member
        simp only [frame835, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h296
        · exact h322
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_south, advanceAt296_north, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt270_south, h270, h296, h322, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_south, advanceAt296_north, advanceAt296_south, advanceAt322_south, advanceAt348_south, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt270_south, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover538 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .east = some outcome) : OracleCovered rowCases538 p outcome := by
  cases h270 : p 270 with
  | false =>
    cases h271 : p 271 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .east = some (.walk 271) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_east, advanceAt271_east, advanceAt271_west, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt270_east, h270, h271, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case512.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case512, memberCase512, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame512.bindings p
      intro binding member
      simp only [frame512, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h270
      · exact h271
    | true =>
      cases h272 : p 272 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .east = some (.push 271 (.stay 272)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_east, advanceAt271_east, advanceAt271_west, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt270_east, h270, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case820.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case820, memberCase820, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame820.bindings p
        intro binding member
        simp only [frame820, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h270
        · exact h271
        · exact h272
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_east, advanceAt271_east, advanceAt271_west, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt270_east, h270, h271, h272, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt270_east, advanceAt271_east, advanceAt271_west, advanceAt272_east, advanceAt273_east, advanceAt274_east, advanceAt275_east, advanceAt276_east, advanceAt277_east, advanceAt278_east, advanceAt279_east, advanceAt280_east, advanceAt281_east, advanceAt282_east, advanceAt283_east, advanceAt284_east, advanceAt285_east, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, floorAt273, doorAt273, trapAt273, boxAt273, holeAt273, floorAt274, doorAt274, trapAt274, boxAt274, holeAt274, floorAt275, doorAt275, trapAt275, boxAt275, holeAt275, floorAt276, doorAt276, trapAt276, boxAt276, holeAt276, floorAt277, doorAt277, trapAt277, boxAt277, holeAt277, floorAt278, doorAt278, trapAt278, boxAt278, holeAt278, floorAt279, doorAt279, trapAt279, boxAt279, holeAt279, floorAt280, doorAt280, trapAt280, boxAt280, holeAt280, floorAt281, doorAt281, trapAt281, boxAt281, holeAt281, floorAt282, doorAt282, trapAt282, boxAt282, holeAt282, floorAt283, doorAt283, trapAt283, boxAt283, holeAt283, floorAt284, doorAt284, trapAt284, boxAt284, holeAt284, floorAt285, doorAt285, trapAt285, boxAt285, holeAt285, cornerAt270_east, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover539 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .west = some outcome) : OracleCovered rowCases539 p outcome := by
  cases h270 : p 270 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_west, advanceAt265_west, advanceAt266_west, advanceAt267_west, advanceAt268_west, advanceAt269_east, advanceAt269_west, advanceAt270_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt270_west, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 2) p) (project (soko1_2.initial.holes.drop 2)) 270 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt260_west, advanceAt261_west, advanceAt262_west, advanceAt263_west, advanceAt264_west, advanceAt265_west, advanceAt266_west, advanceAt267_west, advanceAt268_west, advanceAt269_east, advanceAt269_west, advanceAt270_west, floorAt260, doorAt260, trapAt260, boxAt260, holeAt260, floorAt261, doorAt261, trapAt261, boxAt261, holeAt261, floorAt262, doorAt262, trapAt262, boxAt262, holeAt262, floorAt263, doorAt263, trapAt263, boxAt263, holeAt263, floorAt264, doorAt264, trapAt264, boxAt264, holeAt264, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt266, doorAt266, trapAt266, boxAt266, holeAt266, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, floorAt268, doorAt268, trapAt268, boxAt268, holeAt268, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt270_west, h270, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P02
