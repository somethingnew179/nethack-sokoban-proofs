import NetHack.Soko22Hazard87.OracleCases10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem oracleCover0 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .north = some outcome) :
    OracleCovered rowCases0 p outcome := by
  cases h25 : p 25 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt3_south, advanceAt25_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, cornerAt25_north, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt3_north, advanceAt3_south, advanceAt25_north, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, cornerAt25_north, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover1 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .south = some outcome) :
    OracleCovered rowCases1 p outcome := by
  cases h25 : p 25 with
  | false =>
    cases h47 : p 47 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .south = some (.walk 47) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt47_north, advanceAt47_south, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt25_south, h25, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 47) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 47), d51640), oracleMember0, same, ?_⟩
      simp only [d51639, d51640, d0, d1, h25, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h69 : p 69 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .south = some (.push 47 (.stay 69)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt47_north, advanceAt47_south, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt25_south, h25, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 47 (.stay 69)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 47 (.stay 69)), d53870), oracleMember1, same, ?_⟩
        simp only [d53867, d53869, d53870, d0, d1, h25, h47, h69, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt47_north, advanceAt47_south, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt25_south, h25, h47, h69, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt47_north, advanceAt47_south, advanceAt69_south, advanceAt91_south, advanceAt113_south, advanceAt135_south, advanceAt157_south, advanceAt179_south, advanceAt201_south, advanceAt223_south, advanceAt245_south, advanceAt267_south, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt69, doorAt69, trapAt69, boxAt69, holeAt69, floorAt91, doorAt91, trapAt91, boxAt91, holeAt91, floorAt113, doorAt113, trapAt113, boxAt113, holeAt113, floorAt135, doorAt135, trapAt135, boxAt135, holeAt135, floorAt157, doorAt157, trapAt157, boxAt157, holeAt157, floorAt179, doorAt179, trapAt179, boxAt179, holeAt179, floorAt201, doorAt201, trapAt201, boxAt201, holeAt201, floorAt223, doorAt223, trapAt223, boxAt223, holeAt223, floorAt245, doorAt245, trapAt245, boxAt245, holeAt245, floorAt267, doorAt267, trapAt267, boxAt267, holeAt267, cornerAt25_south, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover2 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .east = some outcome) :
    OracleCovered rowCases2 p outcome := by
  cases h25 : p 25 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_east, advanceAt26_east, advanceAt26_west, advanceAt27_east, advanceAt28_east, advanceAt29_east, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt25_east, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_east, advanceAt26_east, advanceAt26_west, advanceAt27_east, advanceAt28_east, advanceAt29_east, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt25_east, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover3 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .west = some outcome) :
    OracleCovered rowCases3 p outcome := by
  cases h25 : p 25 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_east, advanceAt24_west, advanceAt25_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, cornerAt25_west, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_east, advanceAt24_west, advanceAt25_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, cornerAt25_west, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover4 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northEast = some outcome) :
    OracleCovered rowCases4 p outcome := by
  cases h25 : p 25 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_north, advanceAt25_east, advanceAt25_northEast, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, cornerAt25_northEast, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_north, advanceAt25_east, advanceAt25_northEast, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, cornerAt25_northEast, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover5 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northWest = some outcome) :
    OracleCovered rowCases5 p outcome := by
  cases h25 : p 25 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_north, advanceAt25_west, advanceAt25_northWest, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, cornerAt25_northWest, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_north, advanceAt25_west, advanceAt25_northWest, floorAt2, doorAt2, trapAt2, boxAt2, holeAt2, floorAt3, doorAt3, trapAt3, boxAt3, holeAt3, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, cornerAt25_northWest, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover6 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southEast = some outcome) :
    OracleCovered rowCases6 p outcome := by
  cases h25 : p 25 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h48 : p 48 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southEast = some (.walk 48) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_east, advanceAt25_southEast, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt25_southEast, h25, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 48), d54186), oracleMember2, same, ?_⟩
        simp only [d54184, d54185, d54186, d0, d1, h25, h47, h48, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_east, advanceAt25_southEast, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt25_southEast, h25, h47, h48, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southEast = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_east, advanceAt25_southEast, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt25_southEast, h25, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_east, advanceAt25_southEast, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, cornerAt25_southEast, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover7 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southWest = some outcome) :
    OracleCovered rowCases7 p outcome := by
  cases h25 : p 25 with
  | false =>
    cases h47 : p 47 with
    | false =>
      cases h46 : p 46 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southWest = some (.walk 46) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_west, advanceAt25_southWest, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt25_southWest, h25, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 46) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 46), d54513), oracleMember3, same, ?_⟩
        simp only [d51639, d54512, d54513, d0, d1, h25, h46, h47, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_west, advanceAt25_southWest, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt25_southWest, h25, h46, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_west, advanceAt25_southWest, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt25_southWest, h25, h47, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 25 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt25_south, advanceAt25_west, advanceAt25_southWest, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt46, doorAt46, trapAt46, boxAt46, holeAt46, floorAt47, doorAt47, trapAt47, boxAt47, holeAt47, cornerAt25_southWest, h25, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover8 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .north = some outcome) :
    OracleCovered rowCases8 p outcome := by
  cases h27 : p 27 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt5_south, advanceAt27_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, cornerAt27_north, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt5_north, advanceAt5_south, advanceAt27_north, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, cornerAt27_north, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover9 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .south = some outcome) :
    OracleCovered rowCases9 p outcome := by
  cases h27 : p 27 with
  | false =>
    cases h49 : p 49 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .south = some (.walk 49) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt49_north, advanceAt49_south, advanceAt71_south, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt27_south, h27, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 49), d54518), oracleMember4, same, ?_⟩
      simp only [d54517, d54518, d0, d1, h27, h49, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h71 : p 71 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .south = some (.push 49 (.stay 71)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt49_north, advanceAt49_south, advanceAt71_south, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt27_south, h27, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 49 (.stay 71)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 49 (.stay 71)), d54981), oracleMember5, same, ?_⟩
        simp only [d54978, d54980, d54981, d0, d1, h27, h49, h71, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt49_north, advanceAt49_south, advanceAt71_south, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt27_south, h27, h49, h71, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt49_north, advanceAt49_south, advanceAt71_south, advanceAt93_south, advanceAt115_south, advanceAt137_south, advanceAt159_south, advanceAt181_south, advanceAt203_south, advanceAt225_south, advanceAt247_south, advanceAt269_south, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt71, doorAt71, trapAt71, boxAt71, holeAt71, floorAt93, doorAt93, trapAt93, boxAt93, holeAt93, floorAt115, doorAt115, trapAt115, boxAt115, holeAt115, floorAt137, doorAt137, trapAt137, boxAt137, holeAt137, floorAt159, doorAt159, trapAt159, boxAt159, holeAt159, floorAt181, doorAt181, trapAt181, boxAt181, holeAt181, floorAt203, doorAt203, trapAt203, boxAt203, holeAt203, floorAt225, doorAt225, trapAt225, boxAt225, holeAt225, floorAt247, doorAt247, trapAt247, boxAt247, holeAt247, floorAt269, doorAt269, trapAt269, boxAt269, holeAt269, cornerAt27_south, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover10 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .east = some outcome) :
    OracleCovered rowCases10 p outcome := by
  cases h27 : p 27 with
  | false =>
    cases h28 : p 28 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .east = some (.walk 28) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_east, advanceAt28_east, advanceAt28_west, advanceAt29_east, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt27_east, h27, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 28) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 28), d55597), oracleMember6, same, ?_⟩
      simp only [d55596, d55597, d0, d1, h27, h28, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h29 : p 29 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .east = some (.push 28 (.stay 29)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_east, advanceAt28_east, advanceAt28_west, advanceAt29_east, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt27_east, h27, h28, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 28 (.stay 29)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 28 (.stay 29)), d55749), oracleMember7, same, ?_⟩
        simp only [d55746, d55748, d55749, d0, d1, h27, h28, h29, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_east, advanceAt28_east, advanceAt28_west, advanceAt29_east, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt27_east, h27, h28, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_east, advanceAt28_east, advanceAt28_west, advanceAt29_east, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt27_east, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover11 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .west = some outcome) :
    OracleCovered rowCases11 p outcome := by
  cases h27 : p 27 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_east, advanceAt26_west, advanceAt27_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, cornerAt27_west, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_east, advanceAt26_west, advanceAt27_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, cornerAt27_west, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover12 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northEast = some outcome) :
    OracleCovered rowCases12 p outcome := by
  cases h27 : p 27 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_north, advanceAt27_east, advanceAt27_northEast, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt27_northEast, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_north, advanceAt27_east, advanceAt27_northEast, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt27_northEast, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover13 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northWest = some outcome) :
    OracleCovered rowCases13 p outcome := by
  cases h27 : p 27 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_north, advanceAt27_west, advanceAt27_northWest, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, cornerAt27_northWest, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_north, advanceAt27_west, advanceAt27_northWest, floorAt4, doorAt4, trapAt4, boxAt4, holeAt4, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, cornerAt27_northWest, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover14 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = some outcome) :
    OracleCovered rowCases14 p outcome := by
  cases h27 : p 27 with
  | false =>
    cases h49 : p 49 with
    | false =>
      cases h50 : p 50 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = some (.walk 50) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_east, advanceAt27_southEast, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt27_southEast, h27, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 50), d55757), oracleMember8, same, ?_⟩
        simp only [d55754, d55755, d55756, d55757, d0, d1, h27, h49, h50, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_east, advanceAt27_southEast, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt27_southEast, h27, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h28 : p 28 with
      | false =>
        cases h50 : p 50 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = some (.walk 50) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_east, advanceAt27_southEast, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt27_southEast, h27, h28, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 50), d55757), oracleMember8, same, ?_⟩
          simp only [d55754, d55755, d55756, d55757, d0, d1, h27, h28, h49, h50, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_east, advanceAt27_southEast, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt27_southEast, h27, h28, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_east, advanceAt27_southEast, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt27_southEast, h27, h28, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_east, advanceAt27_southEast, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt27_southEast, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover15 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southWest = some outcome) :
    OracleCovered rowCases15 p outcome := by
  cases h27 : p 27 with
  | false =>
    cases h49 : p 49 with
    | false =>
      cases h48 : p 48 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southWest = some (.walk 48) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_west, advanceAt27_southWest, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt27_southWest, h27, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 48) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 48), d55879), oracleMember9, same, ?_⟩
        simp only [d54517, d55878, d55879, d0, d1, h27, h48, h49, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_west, advanceAt27_southWest, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt27_southWest, h27, h48, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southWest = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_west, advanceAt27_southWest, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt27_southWest, h27, h49, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 27 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt27_south, advanceAt27_west, advanceAt27_southWest, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt48, doorAt48, trapAt48, boxAt48, holeAt48, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, cornerAt27_southWest, h27, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover16 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .north = some outcome) :
    OracleCovered rowCases16 p outcome := by
  cases h28 : p 28 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt6_south, advanceAt28_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_north, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt6_north, advanceAt6_south, advanceAt28_north, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_north, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover17 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .south = some outcome) :
    OracleCovered rowCases17 p outcome := by
  cases h28 : p 28 with
  | false =>
    cases h50 : p 50 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .south = some (.walk 50) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt50_north, advanceAt50_south, advanceAt72_south, advanceAt94_south, advanceAt116_south, advanceAt138_south, advanceAt160_south, advanceAt182_south, advanceAt204_south, advanceAt226_south, advanceAt248_south, advanceAt270_south, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt28_south, h28, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 50), d55880), oracleMember10, same, ?_⟩
      simp only [d55754, d55880, d0, d1, h28, h50, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .south = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt50_north, advanceAt50_south, advanceAt72_south, advanceAt94_south, advanceAt116_south, advanceAt138_south, advanceAt160_south, advanceAt182_south, advanceAt204_south, advanceAt226_south, advanceAt248_south, advanceAt270_south, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt28_south, h28, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt50_north, advanceAt50_south, advanceAt72_south, advanceAt94_south, advanceAt116_south, advanceAt138_south, advanceAt160_south, advanceAt182_south, advanceAt204_south, advanceAt226_south, advanceAt248_south, advanceAt270_south, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt72, doorAt72, trapAt72, boxAt72, holeAt72, floorAt94, doorAt94, trapAt94, boxAt94, holeAt94, floorAt116, doorAt116, trapAt116, boxAt116, holeAt116, floorAt138, doorAt138, trapAt138, boxAt138, holeAt138, floorAt160, doorAt160, trapAt160, boxAt160, holeAt160, floorAt182, doorAt182, trapAt182, boxAt182, holeAt182, floorAt204, doorAt204, trapAt204, boxAt204, holeAt204, floorAt226, doorAt226, trapAt226, boxAt226, holeAt226, floorAt248, doorAt248, trapAt248, boxAt248, holeAt248, floorAt270, doorAt270, trapAt270, boxAt270, holeAt270, cornerAt28_south, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover18 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .east = some outcome) :
    OracleCovered rowCases18 p outcome := by
  cases h28 : p 28 with
  | false =>
    cases h29 : p 29 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .east = some (.walk 29) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_east, advanceAt29_east, advanceAt29_west, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt28_east, h28, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 29) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 29), d55881), oracleMember11, same, ?_⟩
      simp only [d55746, d55881, d0, d1, h28, h29, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h30 : p 30 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .east = some (.push 29 (.stay 30)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_east, advanceAt29_east, advanceAt29_west, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt28_east, h28, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 29 (.stay 30)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 29 (.stay 30)), d55886), oracleMember12, same, ?_⟩
        simp only [d55883, d55885, d55886, d0, d1, h28, h29, h30, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .east = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_east, advanceAt29_east, advanceAt29_west, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt28_east, h28, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_east, advanceAt29_east, advanceAt29_west, advanceAt30_east, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt28_east, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover19 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .west = some outcome) :
    OracleCovered rowCases19 p outcome := by
  cases h28 : p 28 with
  | false =>
    cases h27 : p 27 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .west = some (.walk 27) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_east, advanceAt27_west, advanceAt28_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_west, h27, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 27) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 27), d55597), oracleMember13, same, ?_⟩
      simp only [d55596, d55597, d0, d1, h27, h28, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .west = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_east, advanceAt27_west, advanceAt28_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_west, h27, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_east, advanceAt27_west, advanceAt28_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_west, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover20 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northEast = some outcome) :
    OracleCovered rowCases20 p outcome := by
  cases h28 : p 28 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_north, advanceAt28_east, advanceAt28_northEast, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt28_northEast, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_north, advanceAt28_east, advanceAt28_northEast, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt28_northEast, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover21 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northWest = some outcome) :
    OracleCovered rowCases21 p outcome := by
  cases h28 : p 28 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_north, advanceAt28_west, advanceAt28_northWest, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_northWest, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_north, advanceAt28_west, advanceAt28_northWest, floorAt5, doorAt5, trapAt5, boxAt5, holeAt5, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, cornerAt28_northWest, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover22 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = some outcome) :
    OracleCovered rowCases22 p outcome := by
  cases h28 : p 28 with
  | false =>
    cases h50 : p 50 with
    | false =>
      cases h51 : p 51 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = some (.walk 51) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_east, advanceAt28_southEast, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt28_southEast, h28, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 51), d55894), oracleMember14, same, ?_⟩
        simp only [d55891, d55892, d55893, d55894, d0, d1, h28, h50, h51, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_east, advanceAt28_southEast, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt28_southEast, h28, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h29 : p 29 with
      | false =>
        cases h51 : p 51 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = some (.walk 51) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_east, advanceAt28_southEast, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt28_southEast, h28, h29, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 51), d55894), oracleMember14, same, ?_⟩
          simp only [d55891, d55892, d55893, d55894, d0, d1, h28, h29, h50, h51, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_east, advanceAt28_southEast, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt28_southEast, h28, h29, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_east, advanceAt28_southEast, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt28_southEast, h28, h29, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_east, advanceAt28_southEast, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt28_southEast, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover23 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = some outcome) :
    OracleCovered rowCases23 p outcome := by
  cases h28 : p 28 with
  | false =>
    cases h50 : p 50 with
    | false =>
      cases h49 : p 49 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = some (.walk 49) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_west, advanceAt28_southWest, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt28_southWest, h28, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 49), d56147), oracleMember15, same, ?_⟩
        simp only [d54517, d55754, d55755, d56145, d56146, d56147, d0, d1, h28, h49, h50, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_west, advanceAt28_southWest, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt28_southWest, h28, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h27 : p 27 with
      | false =>
        cases h49 : p 49 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = some (.walk 49) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_west, advanceAt28_southWest, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt28_southWest, h27, h28, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 49) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 49), d56147), oracleMember15, same, ?_⟩
          simp only [d54517, d55754, d55755, d56145, d56146, d56147, d0, d1, h27, h28, h49, h50, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_west, advanceAt28_southWest, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt28_southWest, h27, h28, h49, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_west, advanceAt28_southWest, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt28_southWest, h27, h28, h50, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 28 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt28_south, advanceAt28_west, advanceAt28_southWest, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt49, doorAt49, trapAt49, boxAt49, holeAt49, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, cornerAt28_southWest, h28, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover24 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .north = some outcome) :
    OracleCovered rowCases24 p outcome := by
  cases h29 : p 29 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt7_south, advanceAt29_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_north, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt7_north, advanceAt7_south, advanceAt29_north, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_north, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover25 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .south = some outcome) :
    OracleCovered rowCases25 p outcome := by
  cases h29 : p 29 with
  | false =>
    cases h51 : p 51 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .south = some (.walk 51) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt51_north, advanceAt51_south, advanceAt73_south, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt29_south, h29, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 51) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 51), d56148), oracleMember16, same, ?_⟩
      simp only [d55891, d56148, d0, d1, h29, h51, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h73 : p 73 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .south = some (.push 51 (.stay 73)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt51_north, advanceAt51_south, advanceAt73_south, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt29_south, h29, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 51 (.stay 73)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 51 (.stay 73)), d56153), oracleMember17, same, ?_⟩
        simp only [d56150, d56152, d56153, d0, d1, h29, h51, h73, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt51_north, advanceAt51_south, advanceAt73_south, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt29_south, h29, h51, h73, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt51_north, advanceAt51_south, advanceAt73_south, advanceAt95_south, advanceAt117_south, advanceAt139_south, advanceAt161_south, advanceAt183_south, advanceAt205_south, advanceAt227_south, advanceAt249_south, advanceAt271_south, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt73, doorAt73, trapAt73, boxAt73, holeAt73, floorAt95, doorAt95, trapAt95, boxAt95, holeAt95, floorAt117, doorAt117, trapAt117, boxAt117, holeAt117, floorAt139, doorAt139, trapAt139, boxAt139, holeAt139, floorAt161, doorAt161, trapAt161, boxAt161, holeAt161, floorAt183, doorAt183, trapAt183, boxAt183, holeAt183, floorAt205, doorAt205, trapAt205, boxAt205, holeAt205, floorAt227, doorAt227, trapAt227, boxAt227, holeAt227, floorAt249, doorAt249, trapAt249, boxAt249, holeAt249, floorAt271, doorAt271, trapAt271, boxAt271, holeAt271, cornerAt29_south, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover26 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .east = some outcome) :
    OracleCovered rowCases26 p outcome := by
  cases h29 : p 29 with
  | false =>
    cases h30 : p 30 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .east = some (.walk 30) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_east, advanceAt30_east, advanceAt30_west, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt29_east, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 30) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 30), d56756), oracleMember18, same, ?_⟩
      simp only [d55883, d56756, d0, d1, h29, h30, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .east = none := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_east, advanceAt30_east, advanceAt30_west, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt29_east, h29, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      rw [evaluated] at checked
      cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_east, advanceAt30_east, advanceAt30_west, advanceAt31_east, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt29_east, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover27 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .west = some outcome) :
    OracleCovered rowCases27 p outcome := by
  cases h29 : p 29 with
  | false =>
    cases h28 : p 28 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .west = some (.walk 28) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_east, advanceAt28_west, advanceAt29_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_west, h28, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 28) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 28), d55881), oracleMember19, same, ?_⟩
      simp only [d55746, d55881, d0, d1, h28, h29, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h27 : p 27 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .west = some (.push 28 (.stay 27)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_east, advanceAt28_west, advanceAt29_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_west, h27, h28, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 28 (.stay 27)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 28 (.stay 27)), d55749), oracleMember20, same, ?_⟩
        simp only [d55746, d55748, d55749, d0, d1, h27, h28, h29, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .west = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_east, advanceAt28_west, advanceAt29_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_west, h27, h28, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .west = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt22_west, advanceAt23_west, advanceAt24_west, advanceAt25_west, advanceAt26_west, advanceAt27_west, advanceAt28_east, advanceAt28_west, advanceAt29_west, floorAt22, doorAt22, trapAt22, boxAt22, holeAt22, floorAt23, doorAt23, trapAt23, boxAt23, holeAt23, floorAt24, doorAt24, trapAt24, boxAt24, holeAt24, floorAt25, doorAt25, trapAt25, boxAt25, holeAt25, floorAt26, doorAt26, trapAt26, boxAt26, holeAt26, floorAt27, doorAt27, trapAt27, boxAt27, holeAt27, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_west, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover28 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northEast = some outcome) :
    OracleCovered rowCases28 p outcome := by
  cases h29 : p 29 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_north, advanceAt29_east, advanceAt29_northEast, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt29_northEast, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_north, advanceAt29_east, advanceAt29_northEast, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt29_northEast, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover29 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northWest = some outcome) :
    OracleCovered rowCases29 p outcome := by
  cases h29 : p 29 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_north, advanceAt29_west, advanceAt29_northWest, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_northWest, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .northWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_north, advanceAt29_west, advanceAt29_northWest, floorAt6, doorAt6, trapAt6, boxAt6, holeAt6, floorAt7, doorAt7, trapAt7, boxAt7, holeAt7, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, cornerAt29_northWest, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover30 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = some outcome) :
    OracleCovered rowCases30 p outcome := by
  cases h29 : p 29 with
  | false =>
    cases h51 : p 51 with
    | false =>
      cases h52 : p 52 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = some (.walk 52) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_east, advanceAt29_southEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt29_southEast, h29, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 52) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 52), d56764), oracleMember21, same, ?_⟩
        simp only [d55891, d56761, d56762, d56763, d56764, d0, d1, h29, h51, h52, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_east, advanceAt29_southEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt29_southEast, h29, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h30 : p 30 with
      | false =>
        cases h52 : p 52 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = some (.walk 52) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_east, advanceAt29_southEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt29_southEast, h29, h30, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 52) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 52), d56764), oracleMember21, same, ?_⟩
          simp only [d55891, d56761, d56762, d56763, d56764, d0, d1, h29, h30, h51, h52, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_east, advanceAt29_southEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt29_southEast, h29, h30, h51, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_east, advanceAt29_southEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt29_southEast, h29, h30, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southEast = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_east, advanceAt29_southEast, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, cornerAt29_southEast, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover31 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = some outcome) :
    OracleCovered rowCases31 p outcome := by
  cases h29 : p 29 with
  | false =>
    cases h51 : p 51 with
    | false =>
      cases h50 : p 50 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = some (.walk 50) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_west, advanceAt29_southWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt29_southWest, h29, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.walk 50), d56770), oracleMember22, same, ?_⟩
        simp only [d55754, d55891, d55892, d56768, d56769, d56770, d0, d1, h29, h50, h51, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_west, advanceAt29_southWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt29_southWest, h29, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
    | true =>
      cases h28 : p 28 with
      | false =>
        cases h50 : p 50 with
        | false =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = some (.walk 50) := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_west, advanceAt29_southWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt29_southWest, h28, h29, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          have same : outcome = (.walk 50) := Option.some.inj (checked.symm.trans evaluated)
          refine ⟨((.walk 50), d56770), oracleMember22, same, ?_⟩
          simp only [d55754, d55891, d55892, d56768, d56769, d56770, d0, d1, h28, h29, h50, h51, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
        | true =>
          have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = none := by
            simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_west, advanceAt29_southWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt29_southWest, h28, h29, h50, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
          rw [evaluated] at checked
          cases checked
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_west, advanceAt29_southWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt29_southWest, h28, h29, h51, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 29 .southWest = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt29_south, advanceAt29_west, advanceAt29_southWest, floorAt28, doorAt28, trapAt28, boxAt28, holeAt28, floorAt29, doorAt29, trapAt29, boxAt29, holeAt29, floorAt50, doorAt50, trapAt50, boxAt50, holeAt50, floorAt51, doorAt51, trapAt51, boxAt51, holeAt51, cornerAt29_southWest, h29, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover32 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .north = some outcome) :
    OracleCovered rowCases32 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt8_south, advanceAt30_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_north, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .north = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt8_north, advanceAt8_south, advanceAt30_north, floorAt8, doorAt8, trapAt8, boxAt8, holeAt8, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, cornerAt30_north, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover33 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .south = some outcome) :
    OracleCovered rowCases33 p outcome := by
  cases h30 : p 30 with
  | false =>
    cases h52 : p 52 with
    | false =>
      have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .south = some (.walk 52) := by
        simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt52_north, advanceAt52_south, advanceAt74_south, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt30_south, h30, h52, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
      have same : outcome = (.walk 52) := Option.some.inj (checked.symm.trans evaluated)
      refine ⟨((.walk 52), d56771), oracleMember23, same, ?_⟩
      simp only [d56761, d56771, d0, d1, h30, h52, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
    | true =>
      cases h74 : p 74 with
      | false =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .south = some (.push 52 (.stay 74)) := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt52_north, advanceAt52_south, advanceAt74_south, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt30_south, h30, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        have same : outcome = (.push 52 (.stay 74)) := Option.some.inj (checked.symm.trans evaluated)
        refine ⟨((.push 52 (.stay 74)), d56776), oracleMember24, same, ?_⟩
        simp only [d56773, d56775, d56776, d0, d1, h30, h52, h74, Bool.false_eq_true, ↓reduceIte, ite_self] <;> rfl
      | true =>
        have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .south = none := by
          simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt52_north, advanceAt52_south, advanceAt74_south, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt30_south, h30, h52, h74, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
        rw [evaluated] at checked
        cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .south = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_south, advanceAt52_north, advanceAt52_south, advanceAt74_south, advanceAt96_south, advanceAt118_south, advanceAt140_south, advanceAt162_south, advanceAt184_south, advanceAt206_south, advanceAt228_south, advanceAt250_south, advanceAt272_south, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt52, doorAt52, trapAt52, boxAt52, holeAt52, floorAt74, doorAt74, trapAt74, boxAt74, holeAt74, floorAt96, doorAt96, trapAt96, boxAt96, holeAt96, floorAt118, doorAt118, trapAt118, boxAt118, holeAt118, floorAt140, doorAt140, trapAt140, boxAt140, holeAt140, floorAt162, doorAt162, trapAt162, boxAt162, holeAt162, floorAt184, doorAt184, trapAt184, boxAt184, holeAt184, floorAt206, doorAt206, trapAt206, boxAt206, holeAt206, floorAt228, doorAt228, trapAt228, boxAt228, holeAt228, floorAt250, doorAt250, trapAt250, boxAt250, holeAt250, floorAt272, doorAt272, trapAt272, boxAt272, holeAt272, cornerAt30_south, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
theorem oracleCover34 (p : Pattern) (outcome : HazardPattern.Outcome)
    (checked : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .east = some outcome) :
    OracleCovered rowCases34 p outcome := by
  cases h30 : p 30 with
  | false =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_east, advanceAt31_east, advanceAt31_west, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt30_east, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
  | true =>
    have evaluated : HazardPattern.stepOracle soko2_2.board (HazardPattern.boxes ClosedComponents.soko2_2Support p) (HazardPattern.hazards 10000 soko2_2.initial.holes p) 30 .east = none := by
      simp only [HazardPattern.stepOracle, HazardPattern.pushOracle, HazardPattern.rollOracle, Dir.diagonal, Dir.opposite, advanceAt30_east, advanceAt31_east, advanceAt31_west, advanceAt32_east, advanceAt33_east, advanceAt34_east, advanceAt35_east, advanceAt36_east, advanceAt37_east, advanceAt38_east, advanceAt39_east, advanceAt40_east, advanceAt41_east, advanceAt42_east, advanceAt43_east, floorAt30, doorAt30, trapAt30, boxAt30, holeAt30, floorAt31, doorAt31, trapAt31, boxAt31, holeAt31, floorAt32, doorAt32, trapAt32, boxAt32, holeAt32, floorAt33, doorAt33, trapAt33, boxAt33, holeAt33, floorAt34, doorAt34, trapAt34, boxAt34, holeAt34, floorAt35, doorAt35, trapAt35, boxAt35, holeAt35, floorAt36, doorAt36, trapAt36, boxAt36, holeAt36, floorAt37, doorAt37, trapAt37, boxAt37, holeAt37, floorAt38, doorAt38, trapAt38, boxAt38, holeAt38, floorAt39, doorAt39, trapAt39, boxAt39, holeAt39, floorAt40, doorAt40, trapAt40, boxAt40, holeAt40, floorAt41, doorAt41, trapAt41, boxAt41, holeAt41, floorAt42, doorAt42, trapAt42, boxAt42, holeAt42, floorAt43, doorAt43, trapAt43, boxAt43, holeAt43, cornerAt30_east, h30, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.false_eq_true, ↓reduceIte, bind, pure, Option.bind_some, Option.bind_none] <;> rfl
    rw [evaluated] at checked
    cases checked
end NetHack.Soko22Hazard87
