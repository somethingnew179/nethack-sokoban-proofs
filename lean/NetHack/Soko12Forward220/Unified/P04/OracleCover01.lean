import NetHack.Soko12Forward220.Unified.P04.OracleCover00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko12Forward220.Unified.P04
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover12 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .northEast = some outcome) : OracleCovered rowCases12 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_east, advanceAt30_northEast, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt30_northEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_east, advanceAt30_northEast, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt30_northEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover13 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .northWest = some outcome) : OracleCovered rowCases13 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_west, advanceAt30_northWest, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_northWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_north, advanceAt30_west, advanceAt30_northWest, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_northWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover14 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southEast = some outcome) : OracleCovered rowCases14 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_east, advanceAt30_southEast, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, cornerAt30_southEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_east, advanceAt30_southEast, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, cornerAt30_southEast, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover15 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southWest = some outcome) : OracleCovered rowCases15 p outcome := by
  cases h30 : p 30 with
  | false =>
    cases h56 : p 56 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southWest = some (.walk 55) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt30_southWest, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case006.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case006, memberCase006, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame006.bindings p
      intro binding member
      simp only [frame006, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h30
      · exact h56
    | true =>
      cases h29 : p 29 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southWest = some (.walk 55) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt30_southWest, h29, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = case007.outcome := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨case007, memberCase007, same, ?_⟩
        change DecisionDAGTransform.Satisfies frame007.bindings p
        intro binding member
        simp only [frame007, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact h29
        · exact h30
      | true =>
        have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt30_southWest, h29, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 30 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt30_west, advanceAt30_southWest, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt55, doorAt55, trapAt55, boxAt55, holeAt55, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, cornerAt30_southWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover16 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .north = some outcome) : OracleCovered rowCases16 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .north = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt5_south, advanceAt31_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_north, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover17 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .south = some outcome) : OracleCovered rowCases17 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .south = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_south, advanceAt57_north, advanceAt57_south, advanceAt83_south, advanceAt109_south, advanceAt135_south, advanceAt161_south, advanceAt187_south, advanceAt213_south, advanceAt239_south, advanceAt265_south, advanceAt291_south, advanceAt317_south, advanceAt343_south, advanceAt369_south, advanceAt395_south, advanceAt421_south, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt83, doorAt83, trapAt83, boxAt83, holeAt83, floorAt109, doorAt109, trapAt109, boxAt109, holeAt109, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt187, doorAt187, trapAt187, boxAt187, holeAt187, floorAt213, doorAt213, trapAt213, boxAt213, holeAt213, floorAt239, doorAt239, trapAt239, boxAt239, holeAt239, floorAt265, doorAt265, trapAt265, boxAt265, holeAt265, floorAt291, doorAt291, trapAt291, boxAt291, holeAt291, floorAt317, doorAt317, trapAt317, boxAt317, holeAt317, floorAt343, doorAt343, trapAt343, boxAt343, holeAt343, floorAt369, doorAt369, trapAt369, boxAt369, holeAt369, floorAt395, doorAt395, trapAt395, boxAt395, holeAt395, floorAt421, doorAt421, trapAt421, boxAt421, holeAt421, cornerAt31_south, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover18 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .east = some outcome) : OracleCovered rowCases18 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .east = some (.walk 32) := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_east, advanceAt32_east, advanceAt32_west, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, advanceAt44_east, advanceAt45_east, advanceAt46_east, advanceAt47_east, advanceAt48_east, advanceAt49_east, advanceAt50_east, advanceAt51_east, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, floorAt44, doorAt44, trapAt44, boxAt44, holeAt44, floorAt45, doorAt45, trapAt45, boxAt45, holeAt45, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt31_east, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  have same : outcome = case008.outcome := Option.some.inj (checked.symm.trans evaluated)
  refine ⟨case008, memberCase008, same, ?_⟩
  change DecisionDAGTransform.Satisfies frame008.bindings p
  intro binding member
  cases member
theorem oracleCover19 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .west = some outcome) : OracleCovered rowCases19 p outcome := by
  have area : soko1_2.board.width * soko1_2.board.height = 442 := rfl
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .west = some (.walk 30) := by
      simp only [HazardPattern.stepOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none]
      all_goals simp only [HazardPattern.pushOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none]
      all_goals simp only [HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    have same : outcome = case009.outcome := Option.some.inj (checked.symm.trans evaluated)
    refine ⟨case009, memberCase009, same, ?_⟩
    change DecisionDAGTransform.Satisfies frame009.bindings p
    intro binding member
    simp only [frame009, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl
    · exact h30
  | true =>
    cases h29 : p 29 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .west = some (.push 30 (.stay 29)) := by
        simp only [HazardPattern.stepOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none]
        all_goals simp only [HazardPattern.pushOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none]
        all_goals simp only [HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case673.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case673, memberCase673, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame673.bindings p
      intro binding member
      simp only [frame673, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h29
      · exact h30
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .west = none := by
        simp only [HazardPattern.stepOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none]
        all_goals simp only [HazardPattern.pushOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none]
        all_goals simp only [HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt26_west, advanceAt27_west, advanceAt28_west, advanceAt29_west, advanceAt30_east, advanceAt30_west, advanceAt31_west, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_west, clearAt30_31, clearAt30_32, clearAt30_33, clearAt30_34, clearAt30_35, clearAt30_36, area, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
theorem oracleCover20 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .northEast = some outcome) : OracleCovered rowCases20 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .northEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_north, advanceAt31_east, advanceAt31_northEast, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, cornerAt31_northEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover21 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .northWest = some outcome) : OracleCovered rowCases21 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .northWest = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_north, advanceAt31_west, advanceAt31_northWest, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, cornerAt31_northWest, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover22 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .southEast = some outcome) : OracleCovered rowCases22 p outcome := by
  have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .southEast = none := by
    simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_south, advanceAt31_east, advanceAt31_southEast, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, floorAt58, doorAt58, trapAt58, boxAt58, holeAt58, cornerAt31_southEast, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
  rw [evaluated] at checked
  cases checked
theorem oracleCover23 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .southWest = some outcome) : OracleCovered rowCases23 p outcome := by
  cases h30 : p 30 with
  | false =>
    cases h56 : p 56 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .southWest = some (.walk 56) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_south, advanceAt31_west, advanceAt31_southWest, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, cornerAt31_southWest, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = case010.outcome := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨case010, memberCase010, same, ?_⟩
      change DecisionDAGTransform.Satisfies frame010.bindings p
      intro binding member
      simp only [frame010, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact h30
      · exact h56
    | true =>
      have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_south, advanceAt31_west, advanceAt31_southWest, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, cornerAt31_southWest, h30, h56, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko1_2.board (HazardPattern.boxes (NetHack.SokobanLinearPhases.Map12.crates 4) p) (project (soko1_2.initial.holes.drop 4)) 31 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt31_south, advanceAt31_west, advanceAt31_southWest, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt56, doorAt56, trapAt56, boxAt56, holeAt56, floorAt57, doorAt57, trapAt57, boxAt57, holeAt57, cornerAt31_southWest, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko12Forward220.Unified.P04
