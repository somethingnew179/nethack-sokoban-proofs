import NetHack.Soko12Forward220.Unified.P03.OracleCover56
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P03
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover684 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northEast = some outcome) : OracleCovered rowCases684 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h320 : p 320 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northEast = some (.walk 320) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case622.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case622, memberCase622, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame622.bindings p
        intro binding member
        simp only [frame622, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h319
        · exact h320
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h319, h320, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_east, advanceAt345_northEast, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt320, doorAt320, trapAt320, boxAt320, holeAt320, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, cornerAt345_northEast, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover685 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northWest = some outcome) : OracleCovered rowCases685 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h319 : p 319 with
    | false =>
      cases h318 : p 318 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northWest = some (.walk 318) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h318, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case623.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case623, memberCase623, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame623.bindings p
        intro binding member
        simp only [frame623, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h318
        · exact h319
        · exact h345
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h318, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h319, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_north, advanceAt345_west, advanceAt345_northWest, floorAt318, doorAt318, trapAt318, boxAt318, holeAt318, floorAt319, doorAt319, trapAt319, boxAt319, holeAt319, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, cornerAt345_northWest, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover686 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southEast = some outcome) : OracleCovered rowCases686 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h372 : p 372 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southEast = some (.walk 372) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case624.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case624, memberCase624, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame624.bindings p
        intro binding member
        simp only [frame624, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h345
        · exact h371
        · exact h372
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, h371, h372, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_east, advanceAt345_southEast, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, floorAt372, doorAt372, trapAt372, boxAt372, holeAt372, cornerAt345_southEast, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover687 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southWest = some outcome) : OracleCovered rowCases687 p outcome := by
  cases h345 : p 345 with
  | false =>
    cases h371 : p 371 with
    | false =>
      cases h370 : p 370 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southWest = some (.walk 370) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
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
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, h370, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, h371, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 345 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt345_south, advanceAt345_west, advanceAt345_southWest, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt370, doorAt370, trapAt370, boxAt370, holeAt370, floorAt371, doorAt371, trapAt371, boxAt371, holeAt371, cornerAt345_southWest, h345, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover688 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .north = some outcome) : OracleCovered rowCases688 p outcome := by
  cases h348 : p 348 with
  | false =>
    cases h322 : p 322 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .north = some (.walk 322) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case626.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case626, memberCase626, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame626.bindings p
      intro binding member
      simp only [frame626, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h322
      · exact h348
    | true =>
      cases h296 : p 296 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .north = some (.push 322 (.stay 296)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case844.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case844, memberCase844, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame844.bindings p
        intro binding member
        simp only [frame844, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h296
        · exact h322
        · exact h348
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .north = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h296, h322, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt10_north, advanceAt36_north, advanceAt62_north, advanceAt88_north, advanceAt114_north, advanceAt140_north, advanceAt166_north, advanceAt192_north, advanceAt218_north, advanceAt244_north, advanceAt270_north, advanceAt296_north, advanceAt322_north, advanceAt322_south, advanceAt348_north, floorAt10, doorAt10, trapAt10, boxAt10, holeAt10, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt62, doorAt62, trapAt62, boxAt62, holeAt62, floorAt88, doorAt88, trapAt88, boxAt88, holeAt88, floorAt114, doorAt114, trapAt114, boxAt114, holeAt114, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt166, doorAt166, trapAt166, boxAt166, holeAt166, floorAt192, doorAt192, trapAt192, boxAt192, holeAt192, floorAt218, doorAt218, trapAt218, boxAt218, holeAt218, floorAt244, doorAt244, trapAt244, boxAt244, holeAt244, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, floorAt296, doorAt296, trapAt296, boxAt296, holeAt296, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_north, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover689 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .south = some outcome) : OracleCovered rowCases689 p outcome := by
  cases h348 : p 348 with
  | false =>
    cases h374 : p 374 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .south = some (.walk 374) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case627.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case627, memberCase627, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame627.bindings p
      intro binding member
      simp only [frame627, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h348
      · exact h374
    | true =>
      cases h400 : p 400 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .south = some (.push 374 (.stay 400)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case859.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case859, memberCase859, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame859.bindings p
        intro binding member
        simp only [frame859, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h348
        · exact h374
        · exact h400
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, h374, h400, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt374_north, advanceAt374_south, advanceAt400_south, advanceAt426_south, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt400, doorAt400, trapAt400, boxAt400, holeAt400, floorAt426, doorAt426, trapAt426, boxAt426, holeAt426, cornerAt348_south, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover690 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .east = some outcome) : OracleCovered rowCases690 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_east, advanceAt349_east, advanceAt349_west, advanceAt350_east, advanceAt351_east, advanceAt352_east, advanceAt353_east, advanceAt354_east, advanceAt355_east, advanceAt356_east, advanceAt357_east, advanceAt358_east, advanceAt359_east, advanceAt360_east, advanceAt361_east, advanceAt362_east, advanceAt363_east, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt352, doorAt352, trapAt352, boxAt352, holeAt352, floorAt353, doorAt353, trapAt353, boxAt353, holeAt353, floorAt354, doorAt354, trapAt354, boxAt354, holeAt354, floorAt355, doorAt355, trapAt355, boxAt355, holeAt355, floorAt356, doorAt356, trapAt356, boxAt356, holeAt356, floorAt357, doorAt357, trapAt357, boxAt357, holeAt357, floorAt358, doorAt358, trapAt358, boxAt358, holeAt358, floorAt359, doorAt359, trapAt359, boxAt359, holeAt359, floorAt360, doorAt360, trapAt360, boxAt360, holeAt360, floorAt361, doorAt361, trapAt361, boxAt361, holeAt361, floorAt362, doorAt362, trapAt362, boxAt362, holeAt362, floorAt363, doorAt363, trapAt363, boxAt363, holeAt363, cornerAt348_east, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_east, advanceAt349_east, advanceAt349_west, advanceAt350_east, advanceAt351_east, advanceAt352_east, advanceAt353_east, advanceAt354_east, advanceAt355_east, advanceAt356_east, advanceAt357_east, advanceAt358_east, advanceAt359_east, advanceAt360_east, advanceAt361_east, advanceAt362_east, advanceAt363_east, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt350, doorAt350, trapAt350, boxAt350, holeAt350, floorAt351, doorAt351, trapAt351, boxAt351, holeAt351, floorAt352, doorAt352, trapAt352, boxAt352, holeAt352, floorAt353, doorAt353, trapAt353, boxAt353, holeAt353, floorAt354, doorAt354, trapAt354, boxAt354, holeAt354, floorAt355, doorAt355, trapAt355, boxAt355, holeAt355, floorAt356, doorAt356, trapAt356, boxAt356, holeAt356, floorAt357, doorAt357, trapAt357, boxAt357, holeAt357, floorAt358, doorAt358, trapAt358, boxAt358, holeAt358, floorAt359, doorAt359, trapAt359, boxAt359, holeAt359, floorAt360, doorAt360, trapAt360, boxAt360, holeAt360, floorAt361, doorAt361, trapAt361, boxAt361, holeAt361, floorAt362, doorAt362, trapAt362, boxAt362, holeAt362, floorAt363, doorAt363, trapAt363, boxAt363, holeAt363, cornerAt348_east, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover691 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .west = some outcome) : OracleCovered rowCases691 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt338_west, advanceAt339_west, advanceAt340_west, advanceAt341_west, advanceAt342_west, advanceAt343_west, advanceAt344_west, advanceAt345_west, advanceAt346_west, advanceAt347_east, advanceAt347_west, advanceAt348_west, floorAt338, doorAt338, trapAt338, boxAt338, holeAt338, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_west, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt338_west, advanceAt339_west, advanceAt340_west, advanceAt341_west, advanceAt342_west, advanceAt343_west, advanceAt344_west, advanceAt345_west, advanceAt346_west, advanceAt347_east, advanceAt347_west, advanceAt348_west, floorAt338, doorAt338, trapAt338, boxAt338, holeAt338, floorAt339, doorAt339, trapAt339, boxAt339, holeAt339, floorAt340, doorAt340, trapAt340, boxAt340, holeAt340, floorAt341, doorAt341, trapAt341, boxAt341, holeAt341, floorAt342, doorAt342, trapAt342, boxAt342, holeAt342, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt344, doorAt344, trapAt344, boxAt344, holeAt344, floorAt345, doorAt345, trapAt345, boxAt345, holeAt345, floorAt346, doorAt346, trapAt346, boxAt346, holeAt346, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_west, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover692 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .northEast = some outcome) : OracleCovered rowCases692 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_north, advanceAt348_east, advanceAt348_northEast, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, cornerAt348_northEast, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_north, advanceAt348_east, advanceAt348_northEast, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt323, doorAt323, trapAt323, boxAt323, holeAt323, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, cornerAt348_northEast, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover693 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .northWest = some outcome) : OracleCovered rowCases693 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_north, advanceAt348_west, advanceAt348_northWest, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_northWest, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_north, advanceAt348_west, advanceAt348_northWest, floorAt321, doorAt321, trapAt321, boxAt321, holeAt321, floorAt322, doorAt322, trapAt322, boxAt322, holeAt322, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, cornerAt348_northWest, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover694 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southEast = some outcome) : OracleCovered rowCases694 p outcome := by
  cases h348 : p 348 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt348_east, advanceAt348_southEast, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, cornerAt348_southEast, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt348_east, advanceAt348_southEast, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt349, doorAt349, trapAt349, boxAt349, holeAt349, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, floorAt375, doorAt375, trapAt375, boxAt375, holeAt375, cornerAt348_southEast, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover695 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southWest = some outcome) : OracleCovered rowCases695 p outcome := by
  cases h348 : p 348 with
  | false =>
    cases h374 : p 374 with
    | false =>
      cases h373 : p 373 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southWest = some (.walk 373) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt348_west, advanceAt348_southWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt348_southWest, h348, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case628.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case628, memberCase628, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame628.bindings p
        intro binding member
        simp only [frame628, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact h348
        · exact h373
        · exact h374
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt348_west, advanceAt348_southWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt348_southWest, h348, h373, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt348_west, advanceAt348_southWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt348_southWest, h348, h374, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 3) p) (project (soko1_2.initial.holes.drop 3)) 348 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt348_south, advanceAt348_west, advanceAt348_southWest, floorAt347, doorAt347, trapAt347, boxAt347, holeAt347, floorAt348, doorAt348, trapAt348, boxAt348, holeAt348, floorAt373, doorAt373, trapAt373, boxAt373, holeAt373, floorAt374, doorAt374, trapAt374, boxAt374, holeAt374, cornerAt348_southWest, h348, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P03
